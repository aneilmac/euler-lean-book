import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

-- ANCHOR: simple_soln
def sum_multiple_3_or_5 (n : Nat) : Nat
  := List.range n
  |> List.filter (λ n ↦ n % 5 == 0 || n % 3 == 0)
  |> List.sum
--- ANCHOR_END: simple_soln

-- ANCHOR: eval_simple_soln
#eval sum_multiple_3_or_5 10   -- Prints 23
#eval sum_multiple_3_or_5 1000 -- Prints 233168
-- ANCHOR_END: eval_simple_soln

-- ANCHOR: better_soln
def sum_divisible_by (n t : Nat) : Nat :=
    let p := (n - 1) / t
    t * (p + 1) * p  / 2

def sum_multiple_3_or_5' (n : Nat) : Nat :=
  let sn := sum_divisible_by n
  sn 3 + sn 5 - sn 15
-- ANCHOR_END: better_soln

-- ANCHOR: eval_better_soln
#eval sum_multiple_3_or_5' 10   -- Prints 23
#eval sum_multiple_3_or_5' 1000 -- Prints 233168
-- ANCHOR_END: eval_better_soln

theorem list_range_sum_triangle (n : ℕ) :
  (List.range n).sum = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n' nh =>
    simp [List.range_succ, nh]
    apply Nat.add_right_cancel (m:=n')
    simp [← Nat.triangle_succ]

theorem list_range_sum_triangle' (n : ℕ) :
  (List.range (n + 1)).sum = (n + 1) * n / 2 := list_range_sum_triangle (n + 1)

theorem mod_filter_eq_zero_sum_reduce (n t : ℕ) :
  n % t == 0 -> (List.filter (· % t == 0) [n]).sum = n := by
  intro h;
  unfold List.filter;
  simp [h]

theorem mod_filter_eq_zero_sum_reduce' (n t : ℕ) :
  ¬ (n % t == 0) -> (List.filter (· % t == 0) [n]).sum = 0 := by
  intro h;
  unfold List.filter;
  simp [h]

theorem mod_filter_neq_zero_sum_reduce (n t : ℕ) :
  (n % t == 0) -> (List.filter (· % t != 0) [n]).sum = 0 := by
  intro h;
  unfold List.filter;
  rw [beq_iff_eq] at h
  apply bne_eq_false_iff_eq.mpr at h
  simp [h]

theorem mod_filter_neq_zero_sum_reduce' (n t : ℕ) :
  ¬ (n % t == 0) -> (List.filter (· % t != 0) [n]).sum = n := by
  intro h;
  unfold List.filter;
  rw [beq_iff_eq] at h
  apply bne_iff_ne.mpr at h
  simp [h]

theorem sum_filter_parts_eq_filter_sum (n m : ℕ) :
  (List.range m).sum =
  (List.range m |> List.filter (· % n == 0) |> List.sum) +
  (List.range m |> List.filter (· % n != 0) |> List.sum)
  := by
  induction m with
  | zero => simp
  | succ m' hm =>
    rw [List.range_succ, List.filter_append]
    repeat simp [List.sum_append]
    by_cases nh: (m' % n == 0)
    . simp [mod_filter_eq_zero_sum_reduce m' n nh]
      simp [mod_filter_neq_zero_sum_reduce m' n nh]
      rw [Nat.add_right_comm, hm]
    . simp [mod_filter_eq_zero_sum_reduce' m' n nh]
      simp [mod_filter_neq_zero_sum_reduce' m' n nh]
      simp [← Nat.add_assoc]
      rw [hm]

theorem sum_filter_part_eq_filter_sum_neg (n m : ℕ) :
  (List.range m |> List.filter (· % n == 0) |> List.sum) =
  (List.range m).sum - (List.range m |> List.filter (· % n != 0) |> List.sum)
  := (Nat.sub_eq_of_eq_add (sum_filter_parts_eq_filter_sum n m)).symm

theorem list_filter_eq_nil_sum (l₁ : List ℕ) : (List.filter (· == 0) l₁).sum = 0 := by
  induction l₁ with
  | nil => simp
  | cons n l' lh =>
    simp [List.filter_cons]
    by_cases nh : n = 0 <;> simp [nh, lh]

theorem list_filter_mod_cancel (l₁ : List Nat) : List.filter (· % 1 == 0) l₁ = l₁
  := List.filter_eq_self.mpr (fun x _ ↦ beq_of_eq (Nat.mod_one x))

theorem list_filter_map_add_div (n c : ℕ) (l₁ : List ℕ) : c % n = 0 ->
  List.filter (· % n == 0) (List.map (· * n + c) l₁)  = List.map (· * n + c) l₁ := by
  intro ch
  simp [ch]

theorem list_filter_map (n : ℕ) (l₁ : List ℕ) :
  List.filter (· % n == 0) (List.map (· * n) l₁)  = List.map (· * n) l₁ :=
  list_filter_map_add_div n 0 l₁ (Nat.mod_zero 0)

theorem list_filter_map_add_not_div (n c: ℕ) (l₁ : List ℕ) : c % n ≠ 0 ->
  List.filter (· % n == 0) (List.map (· * n + c) l₁)  = [] := by
  intro ch
  simp [ch]

theorem list_filter_map_add (n c: ℕ) (l₁ : List ℕ) :
   List.filter (· % n == 0) (List.map (· * n + c) l₁) = List.map (· * n + c) l₁ ∨
   List.filter (· % n == 0) (List.map (· * n + c) l₁) = [] := by
   by_cases q: (c % n = 0)
   . exact Or.inl (list_filter_map_add_div n c l₁ q)
   . exact Or.inr (list_filter_map_add_not_div n c l₁ q)

theorem list_map_mul_sum (n : ℕ) (l₁ : List ℕ) : (l₁.map (· * n)).sum = l₁.sum * n := by
  induction l₁ with
  | nil => simp
  | cons m l₁ lh => simp [lh, Nat.add_mul]

theorem list_map_add_sum (n : Nat) (l₁ : List Nat) : (l₁.map (· + n)).sum = l₁.sum + n * l₁.length := by
  induction l₁ with | nil => simp | cons m l₁ lh => simp [lh, Nat.mul_add]; ring

theorem n_div_succ_lt_n_div (n m : ℕ) : 0 < m -> n / (m + 1) ≤ n / m := by
  intro h
  apply Nat.div_le_div_left
  . simp
  . exact h

theorem range_filter_mod_sum_le_eq_zero: ∀ (n m : Nat),
  m ≤ n -> (List.range m |> List.filter (· % n == 0)).sum = 0 := by
  intro n m hn
  have hmod : ∀ x ∈ List.range m, x % n = x := by
    intro x hx
    apply Nat.mod_eq_of_lt
    apply Nat.le_trans (m:=m) (List.mem_range.mp hx) hn
  have hzero: ∀ x ∈ List.range m, (x % n == 0) = (x == 0) := by
    intro x hx
    apply hmod at hx
    rw [hx]
  rw [List.filter_congr hzero]
  apply list_filter_eq_nil_sum

theorem triangle_div_le_eq_zero: ∀ (n m : Nat),
  m ≤ n -> n * ((m - 1) / n + 1) * ((m - 1) / n) / 2 = 0 := by
  intro n m hm
  have: (m - 1) / n = 0 := by
    by_cases q: (m = 0)
    . simp [q]
    . apply Nat.div_eq_of_lt
      apply Nat.le_trans (m:=m)
      rw [← Nat.pred_eq_sub_one]
      apply Nat.pred_lt
      exact q
      exact hm
  simp [this]

theorem list_range_head_zero {m t : Nat} {l : List Nat } (h : List.range m = t :: l  ) : t = 0 := by
  cases m
  . contradiction
  . rw [List.range_succ_eq_map] at h
    rw [List.cons.injEq] at h
    exact h.left.symm

theorem sum_divisible_by_eq_range (n m : Nat):
  sum_divisible_by m n =
  (List.range m |> List.filter (· % n == 0) |> List.sum) := by
  unfold sum_divisible_by; simp
  have (x : Nat) : 2 ∣ (x + 1) * x := by
    induction x with
    | zero => simp
    | succ x' hx =>
      simp [Nat.add_assoc]
      rw [Nat.add_mul, Nat.mul_comm]
      apply Nat.dvd_add
      . exact hx
      . simp
  rw [ Nat.mul_assoc
     , Nat.mul_div_assoc _ (this _)
     , ← list_range_sum_triangle' (n:= (m - 1) / n)
     ]
  by_cases hn : 0 < n
  . have range1 :  List.range 1 = [0] := rfl
    induction m with
    | zero => simp; apply Or.inr; simp [range1]
    | succ m' hm =>
      conv => rhs; rw [List.range_add, range1, List.filter_append, List.sum_append, ← hm]
      unfold List.filter
      simp
      split
      case pos.succ.h_1 hr =>
        apply eq_of_beq at hr
        have hd := Nat.dvd_of_mod_eq_zero hr
        have := Nat.mul_div_cancel' hd
        conv => lhs; simp [List.range_add, range1, Nat.mul_add, this]
        simp; apply Or.inl
        by_cases hz : 0 < m'
        . have : m' / n = (m' - 1) / n + 1 := by
            cases m'
            . contradiction
            . simp; exact Nat.succ_div_of_dvd hd
          rw [← this]
        . simp at hz; rw [hz]; simp [range1]
      case pos.succ.h_2 hr =>
        apply ne_of_beq_false at hr
        simp
        apply Or.inl
        by_cases hz : 0 < m'
        . have : m' / n = (m' - 1) / n := by
            cases m'
            . contradiction
            . simp; exact Nat.succ_div_of_mod_ne_zero hr
          rw [this]
        . simp at hz
          rw [hz]; simp
  . simp at hn
    simp [hn]
    rw [list_filter_eq_nil_sum]

theorem list_sum_not_filter_eq_sum_minus_filter (l₁ : List Nat) (f : ℕ -> Bool) :
  (l₁.filter (not ∘ f)).sum = l₁.sum - (l₁.filter f).sum := by
  induction l₁ with
  | nil => simp
  | cons n l' lh =>
    repeat rw [List.filter_cons]
    split
    case cons.isTrue h =>
      have : f n = false := Lean.Grind.Bool.eq_false_of_not_eq_true h
      simp [this];
      rw [Nat.add_sub_assoc]
      apply congrArg (n + · )
      . exact lh
      . simp [List.Sublist.sum_le_sum _ _]
    case cons.isFalse h =>
      simp at h
      simp [h]
      rw [Nat.add_sub_add_left]
      exact lh

theorem list_sum_not_filter_eq_sum_minus_filter' (l₁ : List Nat) (f : ℕ -> Bool) :
  (l₁.filter (!f ·)).sum = l₁.sum - (l₁.filter f).sum := by
  apply list_sum_not_filter_eq_sum_minus_filter

lemma sum_split (f : Nat -> Bool) (l₁ : List Nat) (n : Nat):
  (if f n then (n :: l₁) else l₁).sum = (if f n then n + l₁.sum else l₁.sum) := by
  split <;> simp

lemma filter_f_g_sum_le_filter_g_sum (f : Nat -> Bool) (g : Nat -> Bool) (ns : List Nat) :
  (List.filter (λ n ↦ f n && g n) ns).sum ≤ (List.filter g ns).sum := by
  induction ns with
  | nil => simp
  | cons n ns' hn =>
    repeat rw [List.filter_cons]
    rw [sum_split (λ n ↦ f n && g n), sum_split (λ n ↦ g n)]
    simp;
    by_cases g n
    case pos h =>
      simp [h]
      split
      . simp [hn]
      . rw [Nat.add_comm]; apply Nat.le_add_right_of_le; exact hn
    by_cases f n
    case pos h =>
      simp [h]
      split
      . apply Nat.add_le_add_left; exact hn
      . exact hn
    case neg hg hf =>
      simp [hg, hf]
      exact hn

lemma filter_or_sum_eq_filter_add (l₁ : List Nat) (f g : ℕ -> Bool) :
  (l₁.filter (λ n ↦ f n || g n)).sum = (l₁.filter f).sum +
  (l₁.filter g).sum - (l₁.filter (λ n ↦ f n && g n)).sum := by
  induction l₁ with
  | nil => simp
  | cons n ns hl =>
    repeat rw [List.filter_cons]
    rw [ sum_split (λ n ↦ f n || g n)
       , sum_split (λ n ↦ f n)
       , sum_split (λ n ↦ g n)
       , sum_split (λ n ↦ f n && g n)
       ]
    simp
    by_cases g n
    case pos hg =>
      repeat rw [hg]
      by_cases f n
      case pos hf =>
        simp [hf]
        rw [Nat.add_sub_assoc, Nat.add_sub_add_left, Nat.add_assoc]
        apply congrArg (n + · )
        rw [← Nat.add_sub_assoc]
        exact hl
        apply filter_f_g_sum_le_filter_g_sum
        apply Nat.add_le_add_left
        apply filter_f_g_sum_le_filter_g_sum
      case neg hf =>
        simp [hf]
        rw [← Nat.add_assoc]
        conv => rhs; lhs; lhs; rw [Nat.add_comm]
        rw [Nat.add_sub_assoc, Nat.add_assoc]
        apply congrArg (n + · )
        rw [← Nat.add_sub_assoc]
        exact hl
        apply filter_f_g_sum_le_filter_g_sum
        apply filter_f_g_sum_le_filter_g_sum
    case neg hg =>
      repeat simp [hg]
      by_cases f n
      case pos hf =>
        simp [hf]
        rw [Nat.add_sub_assoc, Nat.add_assoc]
        apply congrArg (n + · )
        rw [← Nat.add_sub_assoc]
        exact hl
        apply filter_f_g_sum_le_filter_g_sum
        apply filter_f_g_sum_le_filter_g_sum
      case neg hf =>
        simp [hf]
        exact hl
