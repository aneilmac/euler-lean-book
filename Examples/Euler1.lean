import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic


-- ANCHOR: simple_soln
def sum_multiple_3_or_5 (n : Nat) : Nat
  := List.range n
  |> List.filter (λ n ↦ n % 3 == 0 || n % 5 == 0)
  |> List.sum
--- ANCHOR_END: simple_soln

-- ANCHOR: eval_simple_soln
#eval sum_multiple_3_or_5 10   -- Prints 23
#eval sum_multiple_3_or_5 1000 -- Prints 233168
-- ANCHOR_END: eval_simple_soln

-- ANCHOR: better_soln
def sum_divisible_by (t n : Nat) : Nat :=
    let p := (t - 1) / n
    n * (p + 1) * p  / 2

def sum_multiple_3_or_5' (n : Nat) : Nat :=
  let sn := sum_divisible_by n
  sn 3 + sn 5 - sn 15
-- ANCHOR_END: better_soln

-- ANCHOR: eval_better_soln
#eval sum_multiple_3_or_5' 10   -- Prints 23
#eval sum_multiple_3_or_5' 1000 -- Prints 233168
-- ANCHOR_END: eval_better_soln

-- ANCHOR: proof_triangle_list
lemma list_range_sum_triangle (n : Nat) :
  (List.range n).sum = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n' nh =>
    simp [List.range_succ, nh]
    apply Nat.add_right_cancel (m:=n')
    simp [← Nat.triangle_succ]
-- ANCHOR_END: proof_triangle_list

-- ANCHOR: proof_list_range_succ_sum_triangle
lemma list_range_succ_sum_triangle (n : Nat) :
  (List.range (n + 1)).sum = (n + 1) * n / 2 :=
  list_range_sum_triangle (n + 1)
-- ANCHOR_END: proof_list_range_succ_sum_triangle

-- ANCHOR: proof_x_mul_x_succ_dvd_2
lemma x_mul_x_succ_dvd_2 (x : Nat) : 2 ∣ (x + 1) * x := by
  induction x with
  | zero => simp
  | succ x' hx =>
    simp [Nat.add_assoc]
    rw [Nat.add_mul, Nat.mul_comm]
    apply Nat.dvd_add
    . exact hx
    . simp
-- ANCHOR_END: proof_x_mul_x_succ_dvd_2

-- ANCHOR: proof_sum_divisible_by_eq_range_sum
theorem sum_divisible_by_eq_range_sum (n m : Nat):
  sum_divisible_by m n = n * (List.range ((m - 1) / n + 1)).sum := by
  unfold sum_divisible_by
  simp
  rw [ Nat.mul_assoc
     , Nat.mul_div_assoc _ (x_mul_x_succ_dvd_2 _)
     , ← list_range_succ_sum_triangle (n:= (m - 1) / n)
     ]
-- ANCHOR_END: proof_sum_divisible_by_eq_range_sum

-- ANCHOR: proof_range1_eq_zero
lemma range1_eq_zero : List.range 1 = [0] := rfl
-- ANCHOR_END: proof_range1_eq_zero

-- ANCHOR: proof_list_filter_eq_sum
lemma list_filter_eq_nil_sum (ns : List Nat) : (List.filter (· == 0) ns).sum = 0 := by
  induction ns with
  | nil => simp
  | cons n ns' hn =>
    simp [List.filter_cons]
    by_cases nh : n = 0 <;> simp [nh, hn]
-- ANCHOR_END: proof_list_filter_eq_sum


-- ANCHOR: sum_divisible_by_eq_range_filter_sum
theorem sum_divisible_by_eq_range_filter_sum (n m : Nat):
  sum_divisible_by m n =
  ((List.range m).filter (· % n == 0)).sum := by
  rw [sum_divisible_by_eq_range_sum]
  by_cases hzn : 0 < n
  case neg =>
    simp at hzn
    simp [hzn, list_filter_eq_nil_sum]
  case pos =>
    induction m with
    | zero => simp; apply Or.inr; simp [range1_eq_zero]
    | succ m' hm =>
      by_cases hzm : 0 < m'
      case neg => simp at hzm; simp [hzm, range1_eq_zero]
      case pos =>
        conv => rhs
                rw [ List.range_add
                  , range1_eq_zero
                  , List.filter_append
                  , List.sum_append
                  , ← hm ]
        unfold List.filter
        simp; split
        case h_1 hr =>
          apply eq_of_beq at hr
          have := Nat.mul_div_cancel' $ Nat.dvd_of_mod_eq_zero hr
          conv => lhs; simp [List.range_add, range1_eq_zero, Nat.mul_add, this]
          simp; apply Or.inl
          have : m' / n = (m' - 1) / n + 1 := by
            cases m'
            . contradiction
            . simp; exact Nat.succ_div_of_mod_eq_zero hr
          rw [this]
        case h_2 hr =>
          apply ne_of_beq_false at hr
          simp
          apply Or.inl
          have : m' / n = (m' - 1) / n := by
            cases m'
            . contradiction
            . simp; exact Nat.succ_div_of_mod_ne_zero hr
          rw [this]
-- ANCHOR_END: sum_divisible_by_eq_range_filter_sum

-- ANCHOR: proof_filter_f_g_sum_le_filter_g_sum
lemma filter_f_g_sum_le_filter_g_sum (f : Nat -> Bool) (g : Nat -> Bool) (ns : List Nat) :
  (List.filter (λ n ↦ f n && g n) ns).sum ≤ (List.filter g ns).sum := by
  induction ns with
  | nil => simp
  | cons n ns' hn =>
    repeat rw [List.filter_cons]
    by_cases g n
    case pos hg =>
      simp [hg]
      split
      . simp [hn]
      . rw [Nat.add_comm]; apply Nat.le_add_right_of_le; exact hn
    case neg hg => simp [hg]; exact hn
-- ANCHOR_END: proof_filter_f_g_sum_le_filter_g_sum

-- ANCHOR: proof_filter_or_sum_eq_filter_add
lemma filter_or_sum_eq_filter_add (l₁ : List Nat) (f g : Nat -> Bool) :
  (l₁.filter (λ n ↦ f n || g n)).sum = (l₁.filter f).sum +
  (l₁.filter g).sum - (l₁.filter (λ n ↦ f n && g n)).sum := by
  induction l₁ with
  | nil => simp
  | cons n ns hl =>
    repeat rw [List.filter_cons]
    by_cases g n
    case pos hg =>
      repeat rw [hg];
      by_cases f n
      case pos hf =>
        simp [hf]
        rw [ Nat.add_sub_assoc
             (Nat.add_le_add_left (filter_f_g_sum_le_filter_g_sum _ _ _) n)
           , Nat.add_sub_add_left
           , Nat.add_assoc]
        apply congrArg (n + · )
        rw [← Nat.add_sub_assoc (filter_f_g_sum_le_filter_g_sum _ _ _)]
        exact hl
      case neg hf =>
        simp [hf]
        rw [← Nat.add_assoc]
        conv => rhs; lhs; lhs; rw [Nat.add_comm]
        rw [Nat.add_sub_assoc (filter_f_g_sum_le_filter_g_sum _ _ _), Nat.add_assoc]
        apply congrArg (n + · )
        rw [← Nat.add_sub_assoc (filter_f_g_sum_le_filter_g_sum _ _ _)]
        exact hl
    case neg hg =>
      repeat simp [hg]
      by_cases f n
      case pos hf =>
        simp [hf]
        rw [Nat.add_sub_assoc (filter_f_g_sum_le_filter_g_sum _ _ _), Nat.add_assoc]
        apply congrArg (n + · )
        rw [← Nat.add_sub_assoc (filter_f_g_sum_le_filter_g_sum _ _ _)]
        exact hl
      case neg hf =>
        simp [hf]
        exact hl
-- ANCHOR_END: proof_filter_or_sum_eq_filter_add

-- ANCHOR: proof_x_mod_3_and_x_mod_5_eq_mod_15
lemma x_mod_3_and_x_mod_5_eq_mod_15 (n : Nat) : (n % 15 == 0) = (n % 3 == 0 && n % 5 == 0) := by
  have (n : Nat) : n % 15 = 0 ↔ (n % 3 = 0 ∧ n % 5 = 0) := by omega
  by_cases h : (n % 15 = 0)
  case pos => rw [h]; have ⟨h3, h5⟩ := (this n).mp h; simp [h3, h5]
  case neg =>
    rw [beq_eq_false_iff_ne.mpr h]
    apply ((mt (this n).mpr)) at h
    cases Classical.not_and_iff_not_or_not.mp h
      <;> (rename_i h'; simp [h'])
-- ANCHOR_END: proof_x_mod_3_and_x_mod_5_eq_mod_15


-- ANCHOR: proof_sum_divisible_3_5_by_eq_range
theorem sum_divisible_3_5_by_eq_range (n : Nat):
  sum_multiple_3_or_5 n = sum_multiple_3_or_5' n := by
  unfold sum_multiple_3_or_5 sum_multiple_3_or_5'
  simp
  rw [filter_or_sum_eq_filter_add]
  repeat rw [sum_divisible_by_eq_range_filter_sum]
  rw [List.filter_congr λ x a ↦ x_mod_3_and_x_mod_5_eq_mod_15 x]
-- ANCHOR_END: proof_sum_divisible_3_5_by_eq_range
