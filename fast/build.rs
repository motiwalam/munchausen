// With the gpu feature, compile the search shader to SPIR-V with glslc,
// once for each width of digit vectors.
fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    if std::env::var_os("CARGO_FEATURE_GPU").is_none() {
        return;
    }
    println!("cargo::rerun-if-changed=shaders/search.comp");
    let out = std::env::var("OUT_DIR").unwrap();
    for w in [1, 2] {
        let st = std::process::Command::new("glslc")
            .args(["--target-env=vulkan1.3", "-O", &format!("-DW={w}"), "shaders/search.comp", "-o", &format!("{out}/search{w}.spv")])
            .status()
            .expect("the gpu feature needs glslc (from shaderc) on the PATH");
        assert!(st.success(), "glslc failed on shaders/search.comp");
    }
}
