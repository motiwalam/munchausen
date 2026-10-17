// A minimal Vulkan compute context: one queue, host-visible buffers, and
// pipelines that run with a fixed subgroup size.
use ash::vk;
use std::ffi::CStr;

pub struct Gpu {
    _entry: ash::Entry,
    instance: ash::Instance,
    pub device: ash::Device,
    queue: vk::Queue,
    mem_props: vk::PhysicalDeviceMemoryProperties,
    pool: vk::CommandPool,
    cmd: vk::CommandBuffer,
    fence: vk::Fence,
    pub name: String,
}

pub struct Buffer {
    buf: vk::Buffer,
    mem: vk::DeviceMemory,
    ptr: *mut u8,
    pub size: usize,
}

unsafe impl Send for Buffer {}

impl Buffer {
    pub fn bytes(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.size) }
    }
    pub fn bytes_mut(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.size) }
    }
    pub fn u32s(&self) -> &[u32] {
        unsafe { std::slice::from_raw_parts(self.ptr as *const u32, self.size / 4) }
    }
    pub fn u32s_mut(&mut self) -> &mut [u32] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr as *mut u32, self.size / 4) }
    }
}

pub struct Kernel {
    dsl: vk::DescriptorSetLayout,
    layout: vk::PipelineLayout,
    pipeline: vk::Pipeline,
    dpool: vk::DescriptorPool,
    dset: vk::DescriptorSet,
    nbuf: u32,
}

fn err<T>(r: Result<T, vk::Result>, what: &str) -> Result<T, String> {
    r.map_err(|e| format!("{what}: {e:?}"))
}

impl Gpu {
    pub fn new() -> Result<Gpu, String> {
        unsafe {
            let entry = ash::Entry::load().map_err(|e| format!("cannot load Vulkan: {e}"))?;
            let app = vk::ApplicationInfo::default().api_version(vk::make_api_version(0, 1, 3, 0));
            let instance = err(entry.create_instance(&vk::InstanceCreateInfo::default().application_info(&app), None), "create_instance")?;
            let pdevs = err(instance.enumerate_physical_devices(), "enumerate_physical_devices")?;
            let mut pick = None;
            for &pd in &pdevs {
                let props = instance.get_physical_device_properties(pd);
                if props.api_version < vk::make_api_version(0, 1, 3, 0) {
                    continue;
                }
                let qf = instance.get_physical_device_queue_family_properties(pd);
                if let Some(i) = qf.iter().position(|q| q.queue_flags.contains(vk::QueueFlags::COMPUTE)) {
                    let rank = match props.device_type {
                        vk::PhysicalDeviceType::DISCRETE_GPU => 0,
                        vk::PhysicalDeviceType::INTEGRATED_GPU => 1,
                        _ => 2,
                    };
                    if pick.map_or(true, |(_, _, r)| rank < r) {
                        pick = Some((pd, i as u32, rank));
                    }
                }
            }
            let (pd, qfi, rank) = pick.ok_or("no Vulkan 1.3 device with a compute queue")?;
            if rank == 2 {
                return Err("only a software Vulkan device is available".into());
            }
            let props = instance.get_physical_device_properties(pd);
            let name = CStr::from_ptr(props.device_name.as_ptr()).to_string_lossy().into_owned();
            let prio = [1.0f32];
            let qci = [vk::DeviceQueueCreateInfo::default().queue_family_index(qfi).queue_priorities(&prio)];
            let f10 = vk::PhysicalDeviceFeatures::default().shader_int64(true).shader_int16(true);
            let mut f12 = vk::PhysicalDeviceVulkan12Features::default().storage_buffer8_bit_access(true).shader_int8(true);
            let mut f13 = vk::PhysicalDeviceVulkan13Features::default().subgroup_size_control(true).compute_full_subgroups(true);
            let dci = vk::DeviceCreateInfo::default().queue_create_infos(&qci).enabled_features(&f10).push_next(&mut f12).push_next(&mut f13);
            let device = err(instance.create_device(pd, &dci, None), "create_device")?;
            let queue = device.get_device_queue(qfi, 0);
            let mem_props = instance.get_physical_device_memory_properties(pd);
            let pool = err(
                device.create_command_pool(&vk::CommandPoolCreateInfo::default().queue_family_index(qfi).flags(vk::CommandPoolCreateFlags::RESET_COMMAND_BUFFER), None),
                "create_command_pool",
            )?;
            let cmd = err(
                device.allocate_command_buffers(&vk::CommandBufferAllocateInfo::default().command_pool(pool).level(vk::CommandBufferLevel::PRIMARY).command_buffer_count(1)),
                "allocate_command_buffers",
            )?[0];
            let fence = err(device.create_fence(&vk::FenceCreateInfo::default(), None), "create_fence")?;
            Ok(Gpu { _entry: entry, instance, device, queue, mem_props, pool, cmd, fence, name })
        }
    }

    /// A buffer that both the host and the device can access, mapped for its lifetime.
    pub fn buffer(&self, size: usize) -> Result<Buffer, String> {
        let size = size.max(16);
        unsafe {
            let d = &self.device;
            let buf = err(
                d.create_buffer(&vk::BufferCreateInfo::default().size(size as u64).usage(vk::BufferUsageFlags::STORAGE_BUFFER).sharing_mode(vk::SharingMode::EXCLUSIVE), None),
                "create_buffer",
            )?;
            let req = d.get_buffer_memory_requirements(buf);
            let need = vk::MemoryPropertyFlags::HOST_VISIBLE | vk::MemoryPropertyFlags::HOST_COHERENT;
            let mut best: Option<(u32, u32)> = None;
            for i in 0..self.mem_props.memory_type_count {
                let f = self.mem_props.memory_types[i as usize].property_flags;
                if req.memory_type_bits & (1 << i) == 0 || !f.contains(need) {
                    continue;
                }
                let score = f.contains(vk::MemoryPropertyFlags::DEVICE_LOCAL) as u32 * 2 + f.contains(vk::MemoryPropertyFlags::HOST_CACHED) as u32;
                if best.map_or(true, |(_, s)| score > s) {
                    best = Some((i, score));
                }
            }
            let (mt, _) = best.ok_or("no host-visible memory type")?;
            let mem = err(d.allocate_memory(&vk::MemoryAllocateInfo::default().allocation_size(req.size).memory_type_index(mt), None), "allocate_memory")?;
            err(d.bind_buffer_memory(buf, mem, 0), "bind_buffer_memory")?;
            let ptr = err(d.map_memory(mem, 0, vk::WHOLE_SIZE, vk::MemoryMapFlags::empty()), "map_memory")? as *mut u8;
            std::ptr::write_bytes(ptr, 0, size);
            Ok(Buffer { buf, mem, ptr, size })
        }
    }

    pub fn free(&self, b: Buffer) {
        unsafe {
            self.device.unmap_memory(b.mem);
            self.device.destroy_buffer(b.buf, None);
            self.device.free_memory(b.mem, None);
        }
    }

    /// A compute pipeline with `nbuf` storage buffers at bindings 0.., push
    /// constants of `push` bytes, and subgroups of exactly `subgroup` lanes.
    pub fn kernel(&self, spirv: &[u8], nbuf: u32, push: u32, subgroup: u32) -> Result<Kernel, String> {
        unsafe {
            let d = &self.device;
            let words: Vec<u32> = spirv.chunks_exact(4).map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect();
            let module = err(d.create_shader_module(&vk::ShaderModuleCreateInfo::default().code(&words), None), "create_shader_module")?;
            let binds: Vec<_> = (0..nbuf)
                .map(|i| vk::DescriptorSetLayoutBinding::default().binding(i).descriptor_type(vk::DescriptorType::STORAGE_BUFFER).descriptor_count(1).stage_flags(vk::ShaderStageFlags::COMPUTE))
                .collect();
            let dsl = err(d.create_descriptor_set_layout(&vk::DescriptorSetLayoutCreateInfo::default().bindings(&binds), None), "create_descriptor_set_layout")?;
            let ranges = [vk::PushConstantRange::default().stage_flags(vk::ShaderStageFlags::COMPUTE).offset(0).size(push)];
            let dsls = [dsl];
            let mut plci = vk::PipelineLayoutCreateInfo::default().set_layouts(&dsls);
            if push > 0 {
                plci = plci.push_constant_ranges(&ranges);
            }
            let layout = err(d.create_pipeline_layout(&plci, None), "create_pipeline_layout")?;
            let mut sz = vk::PipelineShaderStageRequiredSubgroupSizeCreateInfo::default().required_subgroup_size(subgroup);
            let stage = vk::PipelineShaderStageCreateInfo::default()
                .stage(vk::ShaderStageFlags::COMPUTE)
                .module(module)
                .name(c"main")
                .flags(vk::PipelineShaderStageCreateFlags::REQUIRE_FULL_SUBGROUPS)
                .push_next(&mut sz);
            let pci = [vk::ComputePipelineCreateInfo::default().stage(stage).layout(layout)];
            let pipeline = d.create_compute_pipelines(vk::PipelineCache::null(), &pci, None).map_err(|(_, e)| format!("create_compute_pipelines: {e:?}"))?[0];
            d.destroy_shader_module(module, None);
            let sizes = [vk::DescriptorPoolSize::default().ty(vk::DescriptorType::STORAGE_BUFFER).descriptor_count(nbuf.max(1))];
            let dpool = err(d.create_descriptor_pool(&vk::DescriptorPoolCreateInfo::default().max_sets(1).pool_sizes(&sizes), None), "create_descriptor_pool")?;
            let dset = err(d.allocate_descriptor_sets(&vk::DescriptorSetAllocateInfo::default().descriptor_pool(dpool).set_layouts(&dsls)), "allocate_descriptor_sets")?[0];
            Ok(Kernel { dsl, layout, pipeline, dpool, dset, nbuf })
        }
    }

    pub fn bind(&self, k: &Kernel, bufs: &[&Buffer]) {
        assert_eq!(bufs.len() as u32, k.nbuf);
        let infos: Vec<[vk::DescriptorBufferInfo; 1]> = bufs.iter().map(|b| [vk::DescriptorBufferInfo::default().buffer(b.buf).offset(0).range(vk::WHOLE_SIZE)]).collect();
        let writes: Vec<_> = infos
            .iter()
            .enumerate()
            .map(|(i, info)| vk::WriteDescriptorSet::default().dst_set(k.dset).dst_binding(i as u32).descriptor_type(vk::DescriptorType::STORAGE_BUFFER).buffer_info(info))
            .collect();
        unsafe { self.device.update_descriptor_sets(&writes, &[]) };
    }

    /// Run `groups` workgroups and wait for them to finish.
    pub fn run(&self, k: &Kernel, push: &[u8], groups: u32) -> Result<(), String> {
        unsafe {
            let d = &self.device;
            err(d.reset_command_buffer(self.cmd, vk::CommandBufferResetFlags::empty()), "reset_command_buffer")?;
            err(d.begin_command_buffer(self.cmd, &vk::CommandBufferBeginInfo::default().flags(vk::CommandBufferUsageFlags::ONE_TIME_SUBMIT)), "begin_command_buffer")?;
            d.cmd_bind_pipeline(self.cmd, vk::PipelineBindPoint::COMPUTE, k.pipeline);
            d.cmd_bind_descriptor_sets(self.cmd, vk::PipelineBindPoint::COMPUTE, k.layout, 0, &[k.dset], &[]);
            if !push.is_empty() {
                d.cmd_push_constants(self.cmd, k.layout, vk::ShaderStageFlags::COMPUTE, 0, push);
            }
            d.cmd_dispatch(self.cmd, groups, 1, 1);
            // make the shader's writes visible to the host
            let mb = [vk::MemoryBarrier::default().src_access_mask(vk::AccessFlags::SHADER_WRITE).dst_access_mask(vk::AccessFlags::HOST_READ)];
            d.cmd_pipeline_barrier(self.cmd, vk::PipelineStageFlags::COMPUTE_SHADER, vk::PipelineStageFlags::HOST, vk::DependencyFlags::empty(), &mb, &[], &[]);
            err(d.end_command_buffer(self.cmd), "end_command_buffer")?;
            let cmds = [self.cmd];
            err(d.queue_submit(self.queue, &[vk::SubmitInfo::default().command_buffers(&cmds)], self.fence), "queue_submit")?;
            err(d.wait_for_fences(&[self.fence], true, u64::MAX), "wait_for_fences")?;
            err(d.reset_fences(&[self.fence]), "reset_fences")?;
        }
        Ok(())
    }

    pub fn free_kernel(&self, k: Kernel) {
        unsafe {
            let d = &self.device;
            d.destroy_descriptor_pool(k.dpool, None);
            d.destroy_pipeline(k.pipeline, None);
            d.destroy_pipeline_layout(k.layout, None);
            d.destroy_descriptor_set_layout(k.dsl, None);
        }
    }
}

impl Drop for Gpu {
    fn drop(&mut self) {
        unsafe {
            let _ = self.device.device_wait_idle();
            self.device.destroy_fence(self.fence, None);
            self.device.destroy_command_pool(self.pool, None);
            self.device.destroy_device(None);
            self.instance.destroy_instance(None);
        }
    }
}
