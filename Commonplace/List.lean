import Mathlib.Tactic
import Commonplace.Nat

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

-- ANCHOR: proof_range1_eq_zero
@[simp]
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

theorem list_range_head_zero {m t : Nat} {l : List Nat } (h : List.range m = t :: l  ) : t = 0 := by
  cases m
  . contradiction
  . rw [List.range_succ_eq_map] at h
    rw [List.cons.injEq] at h
    exact h.left.symm

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

lemma even_filter (ns : List Nat) : ∀ x ∈ ns.filter (· % 2 == 0), Even x := by
  intro x h
  apply mod_2_even.mp
  simp
  cases ns with
  | nil => simp at h;
  | cons _ _ =>
    simp at h
    have ⟨h₁, h₂⟩ := h
    exact h₂
