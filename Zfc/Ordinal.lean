import Zfc.Basic

variable [Zf α]

def Zf.IsTransitive (a: α): Prop := ∀x ∈ a, x ⊆ a

def Zf.IsTotalOrder (a: α): Prop := ∀x y, x ∈ a -> y ∈ a -> (x ∈ y ∨ x = y ∨ y ∈ x)

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
  subst z
  have := no_mem_cycle (.tail (.single z_in_y) y_in_x)
  contradiction
  assumption

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
    subst k
    contradiction
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
      apply Or.inl
      rfl
    · subst x
      apply Or.inr
      apply Or.inr
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

def Zf.IsOrdinal.omega :
  Zf.IsOrdinal (Zf.omega: α) := by
  apply Zf.IsOrdinal.mk
  · intro x x_in_omega y y_in_x
    have ⟨ n, _ ⟩  := mem_omega.mp x_in_omega
    subst x
    have ⟨ m, _, _ ⟩  := mem_ofNat.mp y_in_x
    subst y
    apply mem_omega.mpr
    exists m
  · intro x y x_in_omega y_in_omega
    have ⟨ n, _ ⟩  := mem_omega.mp x_in_omega
    subst x
    have ⟨ m, _ ⟩  := mem_omega.mp y_in_omega
    subst y
    clear x_in_omega y_in_omega
    cases h:compare n m
    · apply Or.inl
      apply mem_ofNat.mpr
      exists n
      apply And.intro _ rfl
      exact Nat.compare_eq_lt.mp h
    · apply Or.inr
      apply Or.inl
      congr
      exact Nat.compare_eq_eq.mp h
    · apply Or.inr
      apply Or.inr
      apply mem_ofNat.mpr
      exists m
      apply And.intro _ rfl
      exact Nat.compare_eq_gt.mp h

def Zf.IsOrdinal.ofNat.inj : (Zf.ofNat n: α) = Zf.ofNat m -> n = m := by
  intro h
  induction n generalizing m with
  | zero =>
    match m with
    | 0 => rfl
    | m + 1 =>
      unfold Zf.ofNat at h
      have : (Zf.ofNat m: α) ∈ (Zf.ofNat m)⁺ := mem_succ.mpr (Or.inl rfl)
      rw [←h] at this
      have := not_mem_empty _ this
      contradiction
  | succ n ih =>
    match m with
    | 0 =>
      unfold Zf.ofNat at h
      have : (Zf.ofNat n: α) ∈ (Zf.ofNat n)⁺ := mem_succ.mpr (Or.inl rfl)
      rw [h] at this
      have := not_mem_empty _ this
      contradiction
    | m + 1 =>
      unfold Zf.ofNat at h
      rw [ih]
      apply succ_inj _ _ h
      apply Zf.IsOrdinal.ofNat
      apply Zf.IsOrdinal.ofNat

def Ordinal α [Zf α] := { a: α // Zf.IsOrdinal a }

def Ordinal.mk (a: α) (h: Zf.IsOrdinal a): Ordinal α := ⟨ a, h ⟩

instance Ordinal.ofNat (n: Nat) : Ordinal α := ⟨ Zf.ofNat n, Zf.IsOrdinal.ofNat ⟩

instance Ordinal.OfNat (n: Nat) : OfNat (Ordinal α) n := ⟨ ofNat n ⟩

def Ordinal.omega : Ordinal α := ⟨ Zf.omega, Zf.IsOrdinal.omega ⟩

notation "ω" => Ordinal.omega

@[simp]
instance : LT (Ordinal α) where
  lt a b := a.val ∈ b.val

@[simp]
instance : LE (Ordinal α) where
  le a b := a.val ⊆ b.val

def Ordinal.lt_or_ge (a b: Ordinal α) :
  a < b ∨ a ≥ b := by
  cases Zf.IsOrdinal.mem_total a.property b.property
  apply Or.inl
  assumption
  apply Or.inr
  rename_i h
  cases h
  have : a = b := by cases a <;> cases b <;> congr
  subst b
  apply Zf.sub_refl
  apply a.property.IsTransitive
  assumption

def Ordinal.lt_irrefl (a: Ordinal α) :
  ¬a < a := Zf.mem_irrefl _

def Ordinal.lt_trans {a b c: Ordinal α} :
  a < b -> b < c -> a < c := by
  intro ab bc
  cases a.lt_or_ge c
  · assumption
  · rename_i h
    have := h _ bc
    have := Zf.mem_asymm ab this
    contradiction

def Ordinal.not_lt_of_le {a b: Ordinal α} :
  a ≤ b -> ¬b < a := by
  intro a_le_b b_lt_a
  have := a_le_b b.val b_lt_a
  exact Zf.mem_irrefl _ this

def Ordinal.lt_or_eq_of_le {a b: Ordinal α} :
  a ≤ b -> a < b ∨ a = b := by
  intro ab
  cases Zf.IsOrdinal.mem_total a.property b.property
  · apply Or.inl; assumption
  · rename_i h
    cases h
    · apply Or.inr; cases a; cases b; congr
    · have := Ordinal.not_lt_of_le ab
      contradiction

def Ordinal.lt_of_lt_of_le {a b c: Ordinal α} :
  a < b -> b ≤ c -> a < c := by
  intro ab bc
  cases lt_or_eq_of_le bc
  apply lt_trans <;> assumption
  subst c
  assumption

def Ordinal.lt_of_le_of_lt {a b c: Ordinal α} :
  a ≤ b -> b < c -> a < c := by
  intro ab bc
  cases lt_or_eq_of_le ab
  apply lt_trans <;> assumption
  subst a
  assumption

def Ordinal.le_antisymm {a b: Ordinal α} :
  a ≤ b -> b ≤ a -> a = b := by
  intro ab ba
  cases a ; cases b; congr
  apply Zf.sub_ext <;> assumption

def Ordinal.lt_antisymm {a b: Ordinal α} :
  a < b -> b < a -> False := Zf.mem_asymm

def Ordinal.lt_omega {a: Ordinal α} :
  a < ω -> ∃n, a = OfNat.ofNat n := by
  intro a_lt_omega
  have ⟨ n, prf ⟩  := Zf.mem_omega.mp a_lt_omega
  exists n
  cases a
  congr

def Ordinal.ofNat_le_ofNat :
  (ofNat n: Ordinal α) ≤ ofNat m ↔ n ≤ m:= by
  apply Iff.intro
  intro prf
  have : (OfNat.ofNat n: Ordinal α) < OfNat.ofNat m.succ := by
    apply lt_of_le_of_lt prf
    apply Zf.mem_succ.mpr
    apply Or.inl
    rfl
  have ⟨ m', mle, prf ⟩  := Zf.mem_ofNat.mp this
  have := Zf.IsOrdinal.ofNat.inj prf
  subst m'
  apply Nat.le_of_lt_succ
  assumption
  intro n_le_m
  intro k k_in_n
  apply Zf.mem_ofNat.mpr
  have ⟨ k', k'_lt_n, _ ⟩  := Zf.mem_ofNat.mp k_in_n
  subst k
  exists k'
  apply And.intro _ rfl
  apply Nat.lt_of_lt_of_le
  assumption
  assumption

def Ordinal.ofNat_lt_ofNat :
  (ofNat n: Ordinal α) < ofNat m ↔ n < m:= by
  apply Iff.intro
  intro prf
  have ⟨ _, _, h ⟩  := Zf.mem_ofNat.mp prf
  cases Zf.IsOrdinal.ofNat.inj h
  assumption
  intro n_lt_m
  apply Zf.mem_ofNat.mpr
  exists n

def Ordinal.le_ofNat {a: Ordinal α} :
  a ≤ ofNat n -> ∃m ≤ n, a = ofNat m := by
  intro a_le_ofNat
  have : a < OfNat.ofNat n.succ  := by
    apply lt_of_le_of_lt
    assumption
    apply ofNat_lt_ofNat.mpr
    apply Nat.lt_succ_self
  have ⟨ m, m_lt, prff ⟩  := Zf.mem_ofNat.mp this
  cases a
  exists m
  apply And.intro
  apply Nat.le_of_lt_succ
  assumption
  congr

def Ordinal.lt_ofNat {a: Ordinal α} :
  a < ofNat n -> ∃m < n, a = ofNat m := by
  intro a_lt_ofNat
  have ⟨ m, m_lt, prff ⟩  := Zf.mem_ofNat.mp a_lt_ofNat
  cases a
  exists m
  apply And.intro
  assumption
  congr

def Ordinal.succ (a: Ordinal α) : Ordinal α := Subtype.mk _ a.property.succ

def Ordinal.lt_succ_self (a: Ordinal α) :
  a < a.succ := Zf.mem_succ.mpr (Or.inl rfl)

def Ordinal.IsLimitOrdinal (a: Ordinal α) : Prop := ∀b: Ordinal α, b.succ ≠ a

def Ordinal.zero_le (o: Ordinal α) :
  0 ≤ o := Zf.empty_sub _

def Ordinal.zero_lt_of_ne_zero (o: Ordinal α) :
  o ≠ 0 -> 0 < o := by
  intro ne_zero
  cases lt_or_eq_of_le (Ordinal.zero_le o)
  assumption
  subst o
  contradiction

instance Ordinal.wf : WellFoundedRelation (Ordinal α) where
  rel a b := a < b
  wf := by
    have : @WellFounded α (· ∈ ·) := Zf.wf
    apply WellFounded.intro
    intro a
    cases a with | mk a isord =>
    induction a using this.induction with
    | h a ih =>
    apply Acc.intro
    intro b b_lt_a
    apply ih
    assumption

def Ordinal.induction (motive: Ordinal α -> Prop) :
  (lt: ∀o, (∀x < o, motive x) -> motive o) -> ∀o, motive o := by
  intro lt o
  apply lt
  intro x _
  apply Ordinal.induction
  assumption
termination_by _ o => o

def Ordinal.transfinite_induction (motive: Ordinal α -> Prop) :
  (limit: ∀o: Ordinal α, o.IsLimitOrdinal -> (∀x < o, motive x) -> motive o) ->
  (succ:  ∀o: Ordinal α, motive o -> motive o.succ) -> ∀o, motive o := by
  intro limit succ o
  cases lem (∃o': Ordinal α, o'.succ = o) <;> rename_i h
  · have ⟨ o', _ ⟩ := h
    subst o
    apply succ
    have := lt_succ_self o'
    apply Ordinal.transfinite_induction motive limit succ o'
  · apply limit
    exact not_exists.mp h
    intro x _
    apply Ordinal.transfinite_induction motive limit succ x
termination_by _ _ o => o

def Ordinal.transfinite_induction_with_zero (motive: Ordinal α -> Prop) :
  (zero: motive 0) ->
  (limit: ∀o: Ordinal α, 0 < o -> o.IsLimitOrdinal -> (∀x < o, motive x) -> motive o) ->
  (succ:  ∀o: Ordinal α, motive o -> motive o.succ) -> ∀o, motive o := by
  intro zero limit succ
  apply Ordinal.transfinite_induction
  intro o is_limit x
  cases lem (o = 0)
  subst o
  exact zero
  apply limit
  apply zero_lt_of_ne_zero
  all_goals assumption

def Ordinal.min (a b: Ordinal α) : Ordinal α := by
  apply Subtype.mk (a.val ∩ b.val)
  apply Zf.IsOrdinal.inter
  exact a.property
  exact b.property

def Ordinal.max (a b: Ordinal α) : Ordinal α := by
  apply Subtype.mk (a.val ∪ b.val)
  apply Zf.IsOrdinal.mk
  · intro x x_in_union y y_in_x
    apply Zf.mem_union.mpr
    cases Zf.mem_union.mp x_in_union
    apply Or.inl
    apply a.property.IsTransitive
    assumption
    assumption
    apply Or.inr
    apply b.property.IsTransitive
    assumption
    assumption
  · intro x y x_in_union y_in_union
    apply Zf.IsOrdinal.mem_total
    cases Zf.mem_union.mp x_in_union
    apply a.property.mem; assumption
    apply b.property.mem; assumption
    cases Zf.mem_union.mp y_in_union
    apply a.property.mem; assumption
    apply b.property.mem; assumption

def Ordinal.supremum_of_set (a: α) :
  (∀x ∈ a, Zf.IsOrdinal x) -> Ordinal α := by
  intro mem_ord
  apply Subtype.mk (⋃a)
  apply Zf.IsOrdinal.mk
  · intro x x_in_union y y_in_x
    apply Zf.mem_sUnion.mpr
    have ⟨ w, w_in_a, x_in_w ⟩ := Zf.mem_sUnion.mp x_in_union
    exists w
    apply And.intro
    assumption
    apply (mem_ord w w_in_a).IsTransitive
    assumption
    assumption
  · intro x y x_in_sUnion y_in_sUnion
    have ⟨ x', x'_in_a, x_in_x' ⟩ := Zf.mem_sUnion.mp x_in_sUnion
    have ⟨ y', y'_in_a, y_in_y' ⟩ := Zf.mem_sUnion.mp y_in_sUnion
    apply Zf.IsOrdinal.mem_total
    apply (mem_ord x' x'_in_a).mem
    assumption
    apply (mem_ord y' y'_in_a).mem
    assumption

def Ordinal.infimum_of_set (a: α) :
  a ≠ ∅ ->
  (∀x ∈ a, Zf.IsOrdinal x) -> Ordinal α := by
  intro nonempty_a mem_ord
  apply Subtype.mk (⋂a)
  have ⟨ a', mem ⟩ := Zf.ne_empty_iff_Nonempty.mp nonempty_a
  have mem_sInter := @Zf.mem_sInter α _ _ nonempty_a
  apply Zf.IsOrdinal.mk
  · intro x x_in_union y y_in_x
    apply mem_sInter.mpr
    have h := mem_sInter.mp x_in_union
    intro b b_in_a
    have := h b b_in_a
    apply (mem_ord b b_in_a).IsTransitive
    assumption
    assumption
  · intro x y x_in_sInter y_in_sInter
    have hx := mem_sInter.mp x_in_sInter
    have hy := mem_sInter.mp y_in_sInter
    have a'_ord := mem_ord a' mem
    have := a'_ord.mem _ _ (hx _ mem)
    have := a'_ord.mem _ _ (hy _ mem)
    apply Zf.IsOrdinal.mem_total
    assumption
    assumption

def Ordinal.supremum_of_set_ge (a: α) :
  (mem_ord: ∀x ∈ a, Zf.IsOrdinal x) ->
  ∀x (mem: x ∈ a), (mk x (mem_ord x mem)) ≤ supremum_of_set a mem_ord := by
  intro mem_ord x x_in_a
  unfold mk supremum_of_set
  dsimp
  intro k k_in_X
  apply Zf.mem_sUnion.mpr
  exists x

def Ordinal.infimum_of_set_le (a: α) :
  (nonempty_a: a ≠ ∅) ->
  (mem_ord: ∀x ∈ a, Zf.IsOrdinal x) ->
  ∀x (mem: x ∈ a), infimum_of_set a nonempty_a mem_ord ≤ (mk x (mem_ord x mem)) := by
  intro nonempty_a mem_ord x x_in_a
  unfold mk infimum_of_set
  dsimp
  intro k k_in_sinter
  apply (Zf.mem_sInter nonempty_a).mp k_in_sinter
  assumption

def Ordinal.max_ge_left (a b: Ordinal α): a ≤ a.max b := by
  intro x x_in_a
  apply Zf.mem_union.mpr
  apply Or.inl x_in_a

def Ordinal.max_ge_right (a b: Ordinal α): b ≤ a.max b := by
  intro x x_in_a
  apply Zf.mem_union.mpr
  apply Or.inr x_in_a

def Ordinal.min_le_left (a b: Ordinal α): a.min b ≤ a := by
  intro x x_in_a
  exact (Zf.mem_inter.mp x_in_a).left

def Ordinal.min_le_right (a b: Ordinal α): a.min b ≤ b := by
  intro x x_in_a
  exact (Zf.mem_inter.mp x_in_a).right

def Ordinal.max_comm (a b: Ordinal α): a.max b = b.max a := by
  unfold max
  congr 1
  rw [Zf.union_comm]

def Ordinal.min_comm (a b: Ordinal α): a.min b = b.min a := by
  unfold min
  congr 1
  rw [Zf.inter_comm]

def Ordinal.zero_lt_nonempty (a: Ordinal α) :
  Zf.Nonempty a.val -> 0 < a := by
  intro nonempty_a
  induction a using induction with
  | lt a ih =>
    have ⟨ x, h ⟩ := nonempty_a
    cases lem (x = ∅)
    · subst x
      assumption
    · let x' := mk x ((a.property.mem) _ h)
      have : x' < a := h
      apply lt_trans _ this
      apply ih
      assumption
      apply Zf.ne_empty_iff_Nonempty.mp
      assumption

def Ordinal.supremum (a: Ordinal α) : Ordinal α :=
  supremum_of_set a.val a.property.mem

def Ordinal.infimum (a b: Ordinal α) : b < a -> Ordinal α :=
  fun h =>
  infimum_of_set a.val (Zf.ne_empty_iff_Nonempty.mpr ⟨ _, h ⟩) a.property.mem

def Ordinal.infimum_eq_zero (a b: Ordinal α) (h: b < a) : a.infimum b h = 0 := by
  have := Ordinal.infimum_of_set_le a.val (Zf.ne_empty_iff_Nonempty.mpr ⟨ _, h ⟩) a.property.mem
  have := this ∅ (lt_of_le_of_lt (zero_le _) h)
  apply le_antisymm
  assumption
  apply zero_le

def Ordinal.supremem_succ (a: Ordinal α) : a.succ.supremum = a := by
  unfold supremum supremum_of_set
  cases a with | mk a ord_a =>
  unfold succ
  congr
  dsimp
  apply Zf.ext
  intro x
  apply Iff.intro
  · intro x_in_sunion
    have ⟨ y, y_in_asucc, x_in_y ⟩  := Zf.mem_sUnion.mp x_in_sunion
    cases Zf.mem_succ.mp y_in_asucc
    · subst a; assumption
    · apply ord_a.IsTransitive <;> assumption
  · intro x_in_a
    apply Zf.mem_sUnion.mpr
    exists a
    apply And.intro
    apply Zf.mem_succ.mpr
    apply Or.inl rfl
    assumption

def Ordinal.le_of_lt_succ {a: Ordinal α} :
  ∀{x}, x < a -> x.succ ≤ a := by
  intro x x_lt_a
  intro k k_in_succ
  cases Zf.mem_succ.mp k_in_succ
  subst k
  assumption
  apply a.property.IsTransitive
  assumption
  assumption

def Ordinal.successor_of_limit {a: Ordinal α} :
  a.IsLimitOrdinal ->
  ∀{x}, x < a -> x.succ < a := by
  intro limit x x_lt_a
  cases lt_or_eq_of_le <| le_of_lt_succ x_lt_a
  assumption
  subst a
  have := limit x
  contradiction

def Ordinal.supremem_limit (a: Ordinal α) : a.IsLimitOrdinal -> a.supremum = a := by
  intro limit
  cases a with | mk a ord_a =>
  unfold supremum supremum_of_set
  congr
  dsimp
  apply Zf.ext
  intro x
  apply Iff.intro
  · intro mem_sunion
    have ⟨ y, y_in_a, x_in_y ⟩  := Zf.mem_sUnion.mp mem_sunion
    apply ord_a.IsTransitive
    assumption
    assumption
  · intro x_in_a
    apply Zf.mem_sUnion.mpr
    exists x⁺
    apply And.intro
    let x' := mk x (ord_a.mem _ _ x_in_a)
    have : x' < mk a ord_a := x_in_a
    exact successor_of_limit limit this
    apply Zf.mem_succ.mpr
    apply Or.inl rfl

def Ordinal.addNat (a: Ordinal α) : Nat -> Ordinal α
| 0 => a
| n + 1 => (a.addNat n).succ

instance Ordinal.AddNat : HAdd (Ordinal α) Nat (Ordinal α) := ⟨ addNat ⟩

def Ordinal.addNat_succ (a: Ordinal α) : a + Nat.succ n = (a + n).succ := rfl

def Ordinal.succ_addNat (a: Ordinal α) { n: Nat } :
  a.succ + n = (a + n).succ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [addNat_succ, addNat_succ, ih]
