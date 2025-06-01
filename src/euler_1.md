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
{{#include ../Examples/Euler1.lean:simple_soln}}
```

And, indeed, we get the right answer!

```lean
{{#include ../Examples/Euler1.lean:eval_simple_soln}}
```

## Efficient Solution

The author _hk_ gives a much better way of solving this,
which is much more efficient for larger numbers of `n`.

If we sum the numbers divisible by \\(3\\), and the numbers divisible by \\(5\\) (and take away numbers divisible by \\(15\\) to avoid double counting), then we should get the same answer.

For \\(n=3\\) this is:

\\[3+6+9+12+\dots+999=3 \times (1+2+3+4+\dots+333)\\]

And for \\(n=5\\) we would get:
\\[5+10+15+\dots+995=5\times(1+2+\dots+199)\\]

> [!IMPORTANT]
> Note that \\(199=995/5\\), but also \\(999/5\\) rounded down to the nearest integer.

Now, we know that the sum of a finite set of natural numbers is a [triangle number][Triangle Numbers], that is:

\\[1 + 2 + 3 \dots + p - 1 = \frac{p (p -1)} 2\\]

Which means our lean program becomes:

```lean
{{#include ../Examples/Euler1.lean:better_soln}}
```

And indeed, we get the same answer when we evaluate this number:

```lean
{{#include ../Examples/Euler1.lean:eval_better_soln}}
```

## Proving it

Lean4 is a proof-solving language, so we can take it a step further.
I will present a definition for the theorem to prove that both statements are
equivalent for all natural numbers.

At the very top level we have:

```lean
∀ (n : Nat), sum_multiple_3_or_5 n = sum_multiple_3_or_5' n
```

Which can be unfolded to give the definition:

```lean
(List.filter (λ n ↦ n % 3 == 0 || n % 5 == 0) (List.range n)).sum =
  sum_divisible_by n 3 + sum_divisible_by n 5 - sum_divisible_by n 15
```

Further down the page we [show a proof][sum_divisible_by_eq_range_filter_sum] that `sum_divisible_by n m = (List.filter (λ x ↦ x % m == 0) (List.range n)).sum`. Giving:

```lean
(List.filter (λ n ↦ n % 3 == 0 || n % 5 == 0) (List.range n)).sum =
(List.filter (λ x ↦ x % 3 == 0) (List.range n)).sum + 
(List.filter (λ x ↦ x % 5 == 0) (List.range n)).sum -
(List.filter (λ x ↦ x % 15 == 0) (List.range n)).sum
```

Likewise, we will show an [additional proof][filter_or_sum_eq_filter_add] showing that `(List.filter (λ n ↦ n % 3 == 0 || n % 5 == 0) (List.range n)).sum` is equivelent to:

```lean
(List.filter (λ n ↦ n % 3 == 0) (List.range n)).sum + 
(List.filter (λ n ↦ n % 5 == 0) (List.range n)).sum -
(List.filter (λ n ↦ n % 3 == 0 && n % 5 == 0) (List.range n)).sum
```

giving:

```lean
(List.filter (λ n ↦ n % 3 == 0) (List.range n)).sum + 
(List.filter (λ n ↦ n % 5 == 0) (List.range n)).sum -
(List.filter (λ n ↦ n % 3 == 0 && n % 5 == 0) (List.range n)).sum =
(List.filter (λ x ↦ x % 3 == 0) (List.range n)).sum + 
(List.filter (λ x ↦ x % 5 == 0) (List.range n)).sum -
(List.filter (λ x ↦ x % 15 == 0) (List.range n)).sum
```

Finally, we just need lemma to prove `(λ x ↦ x % 15 == 0)` is equivalent 
to `(λ n ↦ n % 3 == 0 && n % 5 == 0)`. Proven by:

```lean
{{#include ../Examples/Euler1.lean:proof_x_mod_3_and_x_mod_5_eq_mod_15}}
```

Meaning our final proof is:

```lean
{{#include ../Examples/Euler1.lean:proof_sum_divisible_3_5_by_eq_range}}
```

### sum_divisible_by_eq_range_filter_sum 

In this section I will prove the first required theorem:

```lean4
∀ (n m : Nat), 
sum_divisible_by n m = (List.filter (λ x ↦ x % m == 0) (List.range n)).sum
```

To do this we need to prove the relationship between range, sum, and triangle numbers themselves:

```lean
{{#include ../Examples/Euler1.lean:proof_triangle_list}}

{{#include ../Examples/Euler1.lean:proof_list_range_succ_sum_triangle}}
```

Which by induction shows that 

\\[ \texttt{List.range}\left(n\right)\texttt{.sum} = \frac{n \cdot (n - 1)}{2} \\]

and

\\[ \texttt{List.range}\left(n + 1\right)\texttt{.sum} = \frac{(n + 1) \cdot n}{2} \\]


To work with the associativity of divisibility, we also need to prove \\((x + 1) \cdot x\\) is divisible by \\(2\\).

```lean
{{#include ../Examples/Euler1.lean:proof_x_mul_x_succ_dvd_2}}
```

This is enough errata to now satisfy the relationship:

```lean
{{#include ../Examples/Euler1.lean:proof_sum_divisible_by_eq_range_sum}}
```

Which shows that

\\[\begin{eqnarray} 
\frac{n \cdot \left( \frac{m - 1}{n} + 1\right)\left( \frac{m - 1}{n}\right)}{2} = \\\\
n \cdot \frac{\left( \frac{m - 1}{n} + 1\right)\left( \frac{m - 1}{n}\right)}{2} = \\\\
n \cdot \texttt{List.range}\left(\frac{m - 1}{n} + 1\right)\texttt{.sum}
\end{eqnarray}\\]

Next steps are to define the above proof in terms of `filter`. That is:

```lean4
∀ (n m : Nat), 
n * (List.range ((m - 1) / n + 1)).sum = 
(List.filter (fun x ↦ x % n == 0) (List.range m)).sum
```

We must first define some more basic lemma. Both should be fairly obvious:

```lean
{{#include ../Examples/Euler1.lean:proof_range1_eq_zero}}

{{#include ../Examples/Euler1.lean:proof_list_filter_eq_sum}}
```

This is enough to prove our first important theorem `sum_divisible_by_eq_range_filter_sum`.

```lean
{{#include ../Examples/Euler1.lean:sum_divisible_by_eq_range_filter_sum}}
```

### filter_or_sum_eq_filter_add

This theorem is larger.  We need to prove

```lean4
∀ (l₁ : List Nat) (f g : Nat -> Bool),
  (l₁.filter (λ n ↦ f n || g n)).sum = (l₁.filter f).sum +
  (l₁.filter g).sum - (l₁.filter (λ n ↦ f n && g n)).sum 
```


The following lemma is required.

```lean
{{#include ../Examples/Euler1.lean:proof_filter_f_g_sum_le_filter_g_sum}}
```

Which is a long-winded way of stating an obvious fact, that a filter `(f n && g n)` will produce a smaller or equal sum to `g n`.

This allows us to deal with some inequalities produced in our next important proof
`filter_or_sum_eq_filter_add`:

```lean
{{#include ../Examples/Euler1.lean:proof_filter_or_sum_eq_filter_add}}
```

# Conclusion

Thereby, this completes the computer-aided proof of the first Euler problem.

I am not a lean expert. 
It took me 3 weeks to eek this out. 
I don't know why I did this to myself.


[Project Euler]: https://projecteuler.net/problem=1 "Project Euler"
[Triangle Numbers]: https://en.wikipedia.org/wiki/Triangular_number "Triangle Numbers"
[sum_divisible_by_eq_range_filter_sum]: #sum_divisible_by_eq_range_filter_sum "sum_divisible_by_eq_range_filter_sum"
[filter_or_sum_eq_filter_add]: #filter_or_sum_eq_filter_add "filter_or_sum_eq_filter_add"