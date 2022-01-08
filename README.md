# munchausen
Searching for Munchausen Numbers

### Problem statement
Let `F(n, b)` denote the "Munchausen sum" of a number, which is to say the sum of raising each digit of n to its own power, when `n` is represented in base `b`.

A Munchausen number, then, is an `n` such that `F(n, b) = n` for some `b`.

Some examples of Munchausen numbers:
* base 10: `3435 = 3^3 + 4^4 + 3^3 + 5^5 `
* base 17: `54 (base 10) = 33 (base 17) = 3^3 + 3^3`

### Details for the impatient

We search exhaustively. Optimizations detailed below are used to tighten the search space. The current iteration of the algorithm is able to search base 16 in 880 seconds (14 min 40 s).

A list of all Munchausen numbers that have been found so far can be found in `/output`. Files `*-1.txt` employ the `0^0 = 1` convention and files `*-0.txt` employ the `0^0 = 0` convention. Numbers are represented as tuples of digits, and the digits themselves are represented as decimal numerals. More information about the format of the output can be found in `util.py`.

The program is currently written in Python. Its concise and easy to use generator syntax allowed for quick developments on the algorithm. Of course, its speed is an issue and contributions in the form of different language implementations are welcome!

The search also uses multiprocessing module to search different numbers of digits in parallel. We use the `pathos` package's implementation of `multiprocessing` instead of the built-in version because it is able to pickle `lambda` functions.

### A note on convention

What is `0^0`?

Technically, it is undefined. But simply disregarding any number containing the digit 0 seems unsatisfying and needlessly restrictive.

So, what is it then? Well, the consensus seems to be that if we are to give it a value anyway, it should be either 0 or 1.

In our search, we aim to be as accomodating as possible. The search can use either `0^0 = 0` or `0^0 = 1`, depending on a user supplied parameter.

If you're deadset on treating `0^0` as undefined, then you can simply ignore the ones with a zero in them. Doesn't quite the work the other way around though.

### Goal

To find all Munchausen numbers in a given base and to do it as fast as possible.

The long-term goal is to generally characterize the problem of Munchausen numbers and answer the following questions:
* Can we find Munchausen numbers in a given base in polynomial time?
* Is there some sort of general form to a Munchausen number?
* Is it possible to predict how many Munchausen numbers there are in a given base?


### Search

In his [2009 paper](https://arxiv.org/pdf/0911.3038.pdf), Daan van Berkel introduced Munchausen numbers, and established an upperbound of `2b^b` for a given base `b`. That is, there can be no Munchausen number in a base `b` greater than `2b^b`.

Using this upper bound as a starting point, we can search a given base `b` exhaustively to find all Munchausen numbers in that base.

However, since this search space grows exponentially, we need to optimize. The rest of this section will outline the optimizations made.

#### Improving the upper bound

In a base `b>2`, the number `2b^b` starts with the digit 2 and is followed by `b` `0`'s.

Depending on which convention is adopted, this number has a Munchausen sum of either `undefined`, `4`, or `4 + b`. It is clear though, that none of these are equal to `2b^b`, so `2b^b` is not, in and of itself, a Munchausen number.

Thus, any `b+1` digit number in our search space, i.e any number n such that `b^b <= n < 2b^b` must start with the digit 1. This means that the Munchausen sum of `n` is 1 greater than the Munchausen sum of some `b` digit number.

The maximum Munchausen sum of a `b` digit number is if there are `b` copies of the largest digit, so `b(b-1)^(b-1)`. The minimum value for a `b+1` digit number is `b^b`.

Since `1+b(b-1)^(b-1) < b^b` for all natural numbers `b >= 2`, there can never be a `b+1` digit Munchausen number.

Therefore, we can improve our upperbound to only consider `b` digit numbers, or all numbers less than `b^b`.

#### Optimizing the search space

We first notice that the Munchausen sum of a number is agnostic as to the actual order of its digits, meaning that the number `3435` has the same Munchausen sum as `5433` or `4353` or any other permutation. We can significantly reduce our search space by considering unique combinations of digits.

Thus, instead of iterating over each number from 1 to `b^b`, we iterate over the number of digits from 1 to `b`, and generate all possible combinations of that many digits.

Furthermore, for a given number of digits `d` in base `b`, we can exclude some digits from our combinations. If a digit `0 <= x < b` is such that `x^x >= b^d` then it can not possibly appear in a valid d-digit Munchausen number.

As an example, when considering 3-digit combinations in base 10, digits 5 and greater can be ignored, since 5^5 has 4 digits and can not possibly appear in a 3-digit Munchausen number.

Finally, we can also fix some digits in our combinations. Let's refer back to the above example. If we were to restrict our set of possible digits even further to exclude the digit 4, then the maximum obtainable Munchausen sum would be `3 * 3^3 = 81`. Since this has less than 3 digits, we know that the digit 4 must appear at least once. By applying this sort of reasoning at every stage, we can reduce the number of combinations we need to generate. In this example, instead of generating 3-digit combinations from the set `{0, 1, 2, 3, 4}` we can instead generate 2-digit combinations.

The file `nb.py` contains functions that model the sizes of these search spaces and the gains made by each successive optimization.

### A Conjecture

I believe that for `b > 2`, `b` digit Munchausen numbers are not possible. If this conjecture is proven true, it would improve our search space to 75% of what it is currently.

### Next steps

No number of optimizations will make an exhaustive search tractable in the long term. Even with the latest iteration of the algorithm, it took ~17 hours to search base 19 exhaustively. Searching base 20 will require searching ~32 billion combinations of digits.

If we are to really solve this problem, more work needs to be done in terms of studying the characteristics of Munchausen numbers. The next step is to explore ways of explicity constructing Munchausen numbers from the ground up.

That said, there is still a lot of room for improvement in the programming side of things as well. Using a langauge faster than Python might allow for a viable search of the next few bases.
