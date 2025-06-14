# Euler Problem #1

## Problem Statement

[Euler Problem #1][Project Euler] asks:

> If we list all the natural numbers below \\(10\\) that are multiples of \\(3\\) or \\(5\\), we get \\(3, 5, 6\\) and \\(9\\). The sum of these multiples is \\(23\\).  
> Find the sum of all the multiples of \\(3\\) or \\(5\\) below \\(1000\\).

## Simple Solution

The simplest solution is to simply iterate through all numbers, filtering out
those not divisible by 3 or 5, and summing the results. This is fairly trivial
in Lean.


```lean
{{#include ../EulerProblems/Problem1.lean:simple_soln}}
```

And, indeed, we get the right answer!

```lean
{{#include ../EulerProblems/Problem1.lean:eval_simple_soln}}
```

## _hk_'s solution

The author _hk_ gives a much better way of solving this,
which is much more efficient for larger numbers of `n`.

If we sum the numbers divisible by \\(3\\), and the numbers divisible by \\(5\\) (and take away numbers divisible by \\(15\\) to avoid double counting), then we should get the same answer.

For \\(n=3\\) this is:

\\[3+6+9+12+\dots+999=3 \times (1+2+3+4+\dots+333)\\]

And for \\(n=5\\) we would get:
\\[5+10+15+\dots+995=5\times(1+2+\dots+199)\\]

> [!IMPORTANT]
> Note that \\(199=995/5\\), but also \\(199=999/5\\) due to integer rounding.

Now, we know that the sum of a finite set of natural numbers is a [triangle number][Triangle Numbers], that is:

\\[1 + 2 + 3 \dots + p - 1 = \frac{p (p -1)} 2\\]

Meaning we can rewrite the solution as 

```lean
{{#include ../EulerProblems/Problem1.lean:better_soln}}
```

Which for any given chosen input, seems to work:

```lean
{{#include ../EulerProblems/Problem1.lean:eval_better_soln}}
```

## Golfing it

Our aim is to prove that `sum_multiple_3_or_5` and `sum_multiple_3_or_5'` are 
equivalent in lean's proof solving language, to do this, we need to prove that combinations
of `List.range`, `List.sum`, and `List.filter` have simple arithmetic equivalents. 

First, let's focus on the relationship between triangle numbers and sums of lists, which we can prove in lean:

```lean
{{#include ../Commonplace/List.lean:proof_triangle_list}}

{{#include ../Commonplace/List.lean:proof_list_range_succ_sum_triangle}}
```

Meaning we have enough to solve the first step, rewriting `sum_divisible_by` in terms of `List.range` and `List.sum`.

```lean
{{#include ../EulerProblems/Problem1.lean:proof_sum_divisible_by_eq_range_sum}}
```

Next is a much more difficult and unwieldy proof, where we must then rewrite `sum_divisible_by`
in terms of `List.filter`

```lean
{{#include ../EulerProblems/Problem1.lean:sum_divisible_by_eq_range_filter_sum}}
```

This gives us enough of a proof such that  we can now manipulate both functions and show they 
are equivalent


```lean
{{#include ../EulerProblems/Problem1.lean:proof_sum_divisible_3_5_by_eq_range}}
```

[Project Euler]: https://projecteuler.net/problem=1 "Project Euler"
[Triangle Numbers]: https://en.wikipedia.org/wiki/Triangular_number "Triangle Numbers"
