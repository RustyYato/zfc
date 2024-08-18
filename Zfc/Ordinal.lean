import Zfc.Basic

variable [Zf α]

def Zf.IsTransitive (a: α): Prop := ∀x ∈ a, x ⊆ a

def Zf.IsTotalOrder (a: α): Prop := ∀x y, x ∈ a -> y ∈ a -> (x ∈ y ∨ y ∈ x ∨ x = y)

structure Zf.IsOrdinal (a: α): Prop where
  IsTransitive: IsTransitive a
  IsTotalOrder: Zf.IsTotalOrder a

def Zf.IsOrdinal.mem_trans (a: α) :
  IsOrdinal a -> ∀x ∈ a, Zf.IsTransitive x := by
  intro ord_as x x_in_a
  intro y y_in_x z z_in_y
  have y_in_a := ord_as.IsTransitive x x_in_a y y_in_x
  have z_in_a := ord_as.IsTransitive y y_in_a z z_in_y
  cases ord_as.IsTotalOrder x z x_in_a z_in_a <;> rename_i h
  have := no_mem_cycle (.tail (.tail (.single z_in_y) y_in_x) h)
  contradiction
  cases h <;> rename_i h
  assumption
  subst z
  have := no_mem_cycle (.tail (.single z_in_y) y_in_x)
  contradiction

def Zf.IsTransitive.IsOrdinal₀ { a: α } :
  IsTransitive a -> ∀x ∈ a, x ∩ a = x := by
  intro trans_a
  intro x x_in_a
  apply ext
  intro z
  apply Iff.intro
  intro mem
  exact (mem_inter.mp mem).left
  intro z_in_x
  apply mem_inter.mpr
  apply And.intro
  assumption
  apply trans_a
  assumption
  assumption

def Zf.IsOrdinal.mem (x: α) :
  IsOrdinal x -> ∀y ∈ x, Zf.IsOrdinal y := by
  intro ord_x y y_in_x
  apply IsOrdinal.mk
  exact Zf.IsOrdinal.mem_trans x ord_x y y_in_x
  intro a b a_in_y b_in_y
  have := ord_x.IsTransitive y y_in_x
  exact ord_x.IsTotalOrder a b (this a a_in_y) (this b b_in_y)

def Zf.IsLimitOrdinal (a: α) := IsOrdinal a ∧ ∀x, Zf.succ x ≠ a

def Zf.IsOrdinal.sUnion_succ { a: α } :
  IsOrdinal a ->
  ⋃(a⁺) = a := by
  intro ord_a
  rw [succ, insert_def, sUnion_union, sUnion_singleton, union_comm, sub_union]
  intro x mem
  have ⟨ _, _, _ ⟩  := mem_sUnion.mp mem
  apply ord_a.IsTransitive
  assumption
  assumption

def Zf.IsOrdinal.succ_inj { a b: α } :
  IsOrdinal a ->
  IsOrdinal b ->
  a⁺ = b⁺ -> a = b := by
  intro ord_a ord_b succ_eq_succ
  have : ⋃a⁺ = ⋃b⁺ := by
    rw [succ_eq_succ]
  rw [sUnion_succ, sUnion_succ] at this
  exact this
  all_goals assumption

def Zf.IsTransitive.succ_subset_of_mem { a b: α } :
  IsTransitive b ->
  a ∈ b ->
  succ a ⊆ b := by
  intro trans_b a_in_b
  intro x x_in_asucc
  cases mem_succ.mp x_in_asucc
  subst x
  assumption
  apply trans_b
  assumption
  assumption

def Zf.sInter_sub_of_nonempty { a: α }:
  a ≠ ∅ ->
  IsTransitive a ->
  sInter a ⊆ a := by
  intro nonempty_a trans_a b mem
  have := (Zf.mem_sInter nonempty_a).mp mem
  have ⟨ a', a'_in_a ⟩  := Zf.ne_empty_iff_Nonempty.mp nonempty_a
  apply trans_a
  assumption
  apply this
  assumption

def Zf.IsTransitive.IsInitialSegmentOf₀ { X Y: α }:
  IsTransitive X -> IsTransitive Y ->
  Y ∈ X -> IsInitialSegmentOf Y X := by
  intro trans_X trans_Y Y_in_X
  apply And.intro
  apply trans_X
  assumption
  intro x _ y _ x_in_y y_in_Y
  apply trans_Y
  assumption
  assumption

def Zf.IsTransitive.IsInitialSegmentOf₁ { X Y: α }:
  IsTransitive Y ->
  Y ⊆ X -> IsInitialSegmentOf Y X := by
  intro trans_Y Y_sub_X
  apply And.intro
  exact Y_sub_X
  intro x _ y _ x_in_y y_in_Y
  apply trans_Y
  assumption
  assumption

def Zf.IsOrdinal.inter { a b: α } :
  IsOrdinal a ->
  IsOrdinal b ->
  IsOrdinal (a ∩ b) := by
  intro ord_a ord_b
  apply IsOrdinal.mk
  · intro k k_in_inter j j_in_k
    have ⟨ k_in_a, k_in_b ⟩  := mem_inter.mp k_in_inter
    apply mem_inter.mpr
    apply And.intro <;>
      apply IsOrdinal.IsTransitive _ k _ j j_in_k
      <;> assumption
  · intro x y x_in_inter y_in_inter
    have x_in_a := (mem_inter.mp x_in_inter).left
    have y_in_a := (mem_inter.mp y_in_inter).left
    apply ord_a.IsTotalOrder <;> assumption

def Zf.IsOrdinal.ssub_mem { a b: α } :
  IsOrdinal a ->
  IsOrdinal b ->
  a ⊂ b ->
  a ∈ b := by
  intro ord_a ord_b a_ssub_b
  have a_sub_b := a_ssub_b.left

  have := Iff.not_iff_not (@sdiff_empty_iff_sub α _ b a)
  replace := this.mpr (by
    intro b_sub_a
    exact a_ssub_b.right <| Zf.sub_ext a_ssub_b.left b_sub_a)
  have ⟨ s, s_in_sdiff, s_min ⟩  := Zf.exists_min_element b (b \ a) (by
    intro k mem
    exact (mem_sdiff.mp mem).left) (ne_empty_iff_Nonempty.mp this)

  have ⟨ s_in_b, s_notin_a ⟩ := mem_sdiff.mp s_in_sdiff

  have s_sub_a : s ⊆ a := by
    intro k k_in_s
    apply lem.byContradiction
    intro k_not_in_a
    have k_in_b := ord_b.IsTransitive s s_in_b k k_in_s
    have := s_min k (mem_sdiff.mpr ⟨ k_in_b, k_not_in_a ⟩)
    contradiction

  have a_sub_s : a ⊆ s := by
    intro k k_in_a
    apply lem.byContradiction
    intro k_not_in_s
    cases ord_b.IsTotalOrder s k (s_in_b) (a_sub_b k k_in_a) <;> rename_i h
    have := ord_a.IsTransitive k k_in_a s h
    contradiction
    cases h <;> rename_i h
    contradiction
    subst k
    contradiction

  cases Zf.sub_ext a_sub_s s_sub_a
  assumption

def Zf.IsOrdinal.mem_total {a b: α} :
  IsOrdinal a ->
  IsOrdinal b ->
  a ∈ b ∨ a = b ∨ b ∈ a := by
  intro ord_a ord_b
  have sub_left := Zf.inter_sub_left a b
  have sub_right := Zf.inter_sub_right a b

  have ord_inter := Zf.IsOrdinal.inter ord_a ord_b

  cases lem (a ∩ b = a) <;> rename_i inter_eq_a
    <;> (cases lem (a ∩ b = b) <;> rename_i inter_eq_b)
  · have := inter_eq_a.symm.trans inter_eq_b
    apply Or.inr
    apply Or.inl
    assumption
  · have : a ∩ b ⊂ b := ⟨ sub_right, inter_eq_b ⟩
    have := Zf.IsOrdinal.ssub_mem ord_inter ord_b this
    rw [inter_eq_a] at this
    apply Or.inl
    assumption
  · have : a ∩ b ⊂ a := ⟨ sub_left, inter_eq_a ⟩
    have := Zf.IsOrdinal.ssub_mem ord_inter ord_a this
    rw [inter_eq_b] at this
    apply Or.inr
    apply Or.inr
    assumption
  · have : a ∩ b ⊂ a := ⟨ sub_left, inter_eq_a ⟩
    have inter_in_a := Zf.IsOrdinal.ssub_mem ord_inter ord_a this
    have : a ∩ b ⊂ b := ⟨ sub_right, inter_eq_b ⟩
    have inter_in_b := Zf.IsOrdinal.ssub_mem ord_inter ord_b this
    have : a ∩ b ∈ a ∩ b  := mem_inter.mpr ⟨ inter_in_a, inter_in_b ⟩
    have := Zf.mem_irrefl _ this
    contradiction

def Zf.IsOrdinal.zero : IsOrdinal (∅: α) := by
  apply IsOrdinal.mk
  · intro k mem
    have := Zf.not_mem_empty _ mem
    contradiction
  · intro x y mem
    have := Zf.not_mem_empty _ mem
    contradiction

def Zf.IsOrdinal.succ {a: α} :
  IsOrdinal a ->
  IsOrdinal a⁺ := by
  intro ord_a
  apply IsOrdinal.mk
  · intro x x_in_succ y y_in_x
    apply mem_succ.mpr
    cases mem_succ.mp x_in_succ
    subst x
    apply Or.inr
    assumption
    rename_i x_in_a
    apply Or.inr
    exact ord_a.IsTransitive _ x_in_a y y_in_x
  · intro x y x_in_a' y_in_a'
    cases mem_succ.mp x_in_a' <;> cases mem_succ.mp y_in_a'
    . subst x; subst y
      apply Or.inr
      apply Or.inr
      rfl
    · subst x
      apply Or.inr
      apply Or.inl
      assumption
    · subst y
      apply Or.inl
      assumption
    · apply ord_a.IsTotalOrder <;> assumption

def Zf.IsOrdinal.ofNat :
  Zf.IsOrdinal ((ofNat n): α) := by
  induction n with
  | zero => exact IsOrdinal.zero
  | succ n ih => exact ih.succ

def Zf.IsOrdinal.succ_mem_succ { a b: α } :
  IsOrdinal a ->
  IsOrdinal b ->
  a ∈ b ->
  a⁺ ∈ b⁺ := by
  intro ord_a ord_b a_in_b
  cases Zf.IsOrdinal.mem_total ord_a.succ ord_b.succ
  assumption
  rename_i h
  cases h <;> rename_i h
  cases succ_inj ord_a ord_b h
  have := Zf.mem_irrefl _ a_in_b
  contradiction
  cases mem_succ.mp h <;> rename_i h
  subst a
  have := Zf.no_mem_cycle (.tail (.single a_in_b) (mem_succ.mpr (Or.inl rfl)))
  contradiction
  have := Zf.no_mem_cycle (.tail (.tail (.single h) a_in_b) (mem_succ.mpr (Or.inl rfl)))
  contradiction
