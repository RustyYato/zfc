import Zfc.Classical
import Zfc.Wf
import Zfc.AxiomBlame

def succ' (sUnion: α -> α) (pair: α -> α -> α) (a: α) : α :=
  sUnion (pair a (pair a a))

def ofNat' [EmptyCollection α] (sUnion: α -> α) (pair: α -> α -> α)
  : Nat -> α
| 0 => ∅
| n + 1 => succ' sUnion pair (ofNat' sUnion pair n)

def subset' [Membership α α] (x y: α) : Prop := ∀z ∈ x, z ∈ y

class Zf (α: Type _) extends
  Membership α α, EmptyCollection α where
  -- axiom of regularity
  wf : @WellFounded α (· ∈ ·)

  -- axiom of extensionality
  ext: ∀{x y: α}, (∀z, z ∈ x ↔ z ∈ y) -> x = y

  -- axiom of pair
  pair: α -> α -> α
  mem_pair: ∀{x y z: α}, z ∈ pair x y ↔ z = x ∨ z = y

  -- axiom of union
  sUnion: α -> α
  mem_sUnion: ∀{x y: α}, y ∈ sUnion x ↔ ∃z ∈ x, y ∈ z

  -- axiom of powerset
  powerset: α -> α
  mem_powerset': ∀{x y}, y ∈ powerset x ↔ subset' y x

  -- axiom of empty set
  not_mem_empty: ∀x: α, ¬x ∈ (∅: α)

  -- axiom of infinity
  omega: α
  mem_omega': ∀{x}, x ∈ omega ↔ ∃n, x = ofNat' sUnion pair n

  sep: α -> (α -> Prop) -> α
  mem_sep: ∀{x P y}, y ∈ sep x P ↔ y ∈ x ∧ P y

  image: α -> (α -> α) -> α
  mem_image: ∀{x f y}, y ∈ image x f ↔ ∃z ∈ x, y = f z

variable { α: Type _ } [Zf α]

prefix:max "⋃" => Zf.sUnion

def Zf.sInter (a: α) : α :=
  Zf.sep (⋃ a) <| fun x => ∀b ∈ a, x ∈ b

prefix:max "⋂" => Zf.sInter

instance : Union α where
  union a b := ⋃(Zf.pair a b)

instance : Inter α where
  inter a b := ⋂(Zf.pair a b)

def Zf.singleton (a: α) : α := pair a a

instance Zf.SingletonInst : Singleton α α := ⟨ Zf.singleton ⟩

instance Zf.InsertInst : Insert α α where
  insert a b := { a } ∪ b

def Zf.Nonempty (a: α) := ∃x, x ∈ a

def Zf.ne_empty_iff_Nonempty {a: α}:
  a ≠ ∅ ↔ Zf.Nonempty a := by
  apply Iff.intro
  intro a_ne_empty
  apply lem.byContradiction
  intro not_nonempty
  have := not_exists.mp not_nonempty
  apply a_ne_empty
  apply ext
  intro z
  apply Iff.intro
  intro mem
  have := this _ mem
  contradiction
  intro mem
  have := Zf.not_mem_empty _ mem
  contradiction
  intro ne a_eq_empty
  subst a_eq_empty
  have ⟨ _, mem ⟩ := ne
  have := Zf.not_mem_empty _ mem
  contradiction

def Zf.mem_sInter {a: α} :
  a ≠ ∅ -> ∀{x}, x ∈ ⋂ a ↔ ∀b ∈ a, x ∈ b := by
  intro nonempty_a x
  apply Iff.intro
  intro mem_sInter
  intro b b_in_a
  have ⟨ _x_in_sunion, mem_all ⟩ := mem_sep.mp mem_sInter
  apply mem_all
  assumption
  intro mem_sInter
  apply mem_sep.mpr
  apply And.intro
  apply mem_sUnion.mpr
  have ⟨ x, x_in_a ⟩  := ne_empty_iff_Nonempty.mp nonempty_a
  exists x
  apply And.intro x_in_a
  apply mem_sInter
  assumption
  assumption

def Zf.mem_union {a b: α} :
  ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  apply Iff.intro
  intro mem_union
  have ⟨ y, y_in_pair, x_in_y ⟩ := mem_sUnion.mp mem_union
  cases mem_pair.mp y_in_pair <;> subst y
  apply Or.inl; assumption
  apply Or.inr; assumption
  intro mem
  apply mem_sUnion.mpr
  cases mem
  exists a
  apply And.intro
  apply mem_pair.mpr
  apply Or.inl; rfl
  assumption
  exists b
  apply And.intro
  apply mem_pair.mpr
  apply Or.inr; rfl
  assumption

def Zf.mem_inter {a b: α} :
  ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  intro x
  have nonempty_pair: Zf.Nonempty (pair a b) := ⟨ _, mem_pair.mpr (Or.inl rfl) ⟩
  have mem_sInter := @mem_sInter _ _ _ (Zf.ne_empty_iff_Nonempty.mpr nonempty_pair)
  apply Iff.intro
  intro mem_inter
  apply And.intro
  <;> apply mem_sInter.mp mem_inter
  apply mem_pair.mpr
  apply Or.inl rfl
  apply mem_pair.mpr
  apply Or.inr rfl
  intro mem
  apply mem_sInter.mpr
  intro y y_in_pair
  cases mem_pair.mp y_in_pair <;> subst y
  exact mem.left
  exact mem.right

def Zf.mem_singleton [Zf α] { a: α } :
  ∀{x}, x ∈ ({ a }: α) ↔ x = a := by
  intro x
  apply Iff.intro
  intro mem_singleton
  cases mem_pair.mp mem_singleton <;> assumption
  intro x
  apply mem_pair.mpr
  apply Or.inl; assumption

def Zf.mem_insert [Zf α] { a b: α } :
  ∀{x}, x ∈ insert a b ↔ x = a ∨ x ∈ b := by
  intro x
  apply Iff.intro
  intro mem_insert
  cases mem_union.mp mem_insert
  apply Or.inl
  apply mem_singleton.mp
  assumption
  apply Or.inr
  assumption
  intro mem
  apply mem_union.mpr
  cases mem
  apply Or.inl
  apply mem_singleton.mpr
  assumption
  apply Or.inr
  assumption

instance Zf.SubsetInst : HasSubset α where
  Subset a b := ∀x ∈ a, x ∈ b

instance Zf.SSubsetInst : HasSSubset α where
  SSubset a b := a ⊆ b ∧ a ≠ b

instance Zf.SDiff : SDiff α where
  sdiff a b := Zf.sep a <| fun x => x ∉ b

def Zf.mem_sdiff { a b: α } :
  ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := Zf.mem_sep

def Zf.succ (a: α) : α := insert a a

postfix:max "⁺" => Zf.succ

def Zf.ofNat : Nat -> α
| 0 => ∅
| n + 1 => (ofNat n)⁺

def Zf.mem_succ { a: α } :
  ∀{x}, x ∈ a⁺ ↔ x = a ∨ x ∈ a := mem_insert

def Zf.mem_ofNat :
  ∀{x}, x ∈ (ofNat n: α) ↔ ∃m < n, x = ofNat m := by
  induction n with
  | zero =>
    intro x
    apply Iff.intro
    intro mem
    have := Zf.not_mem_empty _ mem
    contradiction
    intro mem
    have ⟨ _, h, _ ⟩ := mem
    have := Nat.not_lt_zero _ h
    contradiction
  | succ n ih =>
    intro x
    apply Iff.intro
    · intro mem
      cases mem_succ.mp mem
      subst x
      exists n
      apply And.intro
      apply Nat.lt_succ_self
      rfl
      rename_i h
      have ⟨ m, m_lt_n, prf ⟩  := ih.mp h
      exists m
      apply And.intro
      apply Nat.lt_trans
      assumption
      apply Nat.lt_succ_self
      assumption
    · intro mem
      have ⟨ m, m_lt_n, prf ⟩ := mem
      subst x
      clear mem
      apply mem_succ.mpr
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ m_lt_n)
      apply Or.inr
      apply ih.mpr
      exists m
      subst n
      apply Or.inl
      rfl

def Zf.pair_comm (a b: α) : pair a b = pair b a := by
  apply ext
  intro z
  apply Iff.intro
  intro mem
  apply mem_pair.mpr
  cases mem_pair.mp mem
  apply Or.inr; assumption
  apply Or.inl; assumption
  intro mem
  apply mem_pair.mpr
  cases mem_pair.mp mem
  apply Or.inr; assumption
  apply Or.inl; assumption

def Zf.union_def (a b: α) : ⋃(pair a b) = a ∪ b := rfl
def Zf.inter_def (a b: α) : ⋂(pair a b) = a ∩ b := rfl
def Zf.singleton_def (a: α) : singleton a = { a } := rfl
def Zf.insert_def (a b: α) : insert a b = { a } ∪ b := rfl

def ofNat_eq_ofNat' :
  ((Zf.ofNat n): α) = ofNat' Zf.sUnion Zf.pair n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Zf.ofNat ofNat'
    apply Zf.ext
    intro x
    apply Iff.intro
    · intro x_in_succ
      unfold succ'
      rw [←ih, ←Zf.singleton, Zf.pair_comm, Zf.union_def, Zf.singleton_def, ←Zf.insert_def]
      apply Zf.mem_insert.mpr
      cases Zf.mem_succ.mp x_in_succ
      apply Or.inl; assumption
      apply Or.inr; assumption
    · intro x_in_succ'
      have ⟨ y, y_in_pair, x_in_y ⟩  := Zf.mem_sUnion.mp x_in_succ'
      apply Zf.mem_insert.mpr
      rw [ih]
      cases Zf.mem_pair.mp y_in_pair
      subst y
      apply Or.inr
      assumption
      subst y
      apply Or.inl
      cases Zf.mem_pair.mp x_in_y <;> assumption

def Zf.mem_omega :
  ∀{x}, x ∈ (Zf.omega: α) ↔ ∃n, x = ofNat n := by
  intro x
  apply Iff.intro
  · intro mem_omega
    have ⟨ n, x_eq ⟩  := Zf.mem_omega'.mp mem_omega
    subst x
    exists n
    clear mem_omega
    rw [ofNat_eq_ofNat']
  · intro ex
    apply mem_omega'.mpr
    have ⟨ n, _ ⟩ := ex
    subst x
    exists n
    clear ex
    rw [ofNat_eq_ofNat']

def Zf.mem_irrefl (a: α) : a ∉ a := WellFounded.irrefl Zf.wf
def Zf.mem_asymm {a b: α} : a ∈ b -> b ∉ a := WellFounded.asymm Zf.wf
def Zf.ne_of_mem {a b: α} : a ∈ b -> a ≠ b := by
  intro mem h
  subst a
  exact Zf.mem_irrefl _ mem

def Zf.sUnion_union { a b: α } :
  ⋃(a ∪ b) = ⋃a ∪ ⋃b := by
  apply ext
  intro x
  apply Iff.intro
  intro mem
  apply mem_union.mpr
  have ⟨ y, y_in_union, x_in_y ⟩ := mem_sUnion.mp mem
  cases mem_union.mp y_in_union
  apply Or.inl
  apply mem_sUnion.mpr
  exists y
  apply Or.inr
  apply mem_sUnion.mpr
  exists y
  intro mem
  cases mem_union.mp mem <;> rename_i mem
  cases mem_sUnion.mp mem <;> rename_i w prf
  cases prf <;> rename_i prf₀ prf₁
  apply mem_sUnion.mpr
  exists w
  apply And.intro
  apply mem_union.mpr
  apply Or.inl; assumption; assumption
  cases mem_sUnion.mp mem <;> rename_i w prf
  cases prf <;> rename_i prf₀ prf₁
  apply mem_sUnion.mpr
  exists w
  apply And.intro
  apply mem_union.mpr
  apply Or.inr; assumption; assumption

def Zf.sUnion_singleton { a: α }:
  ⋃{ a } = a := by
  apply ext
  intro  x
  apply Iff.intro
  intro mem
  have ⟨ _, mem, _ ⟩ := mem_sUnion.mp mem
  cases mem_singleton.mp mem
  assumption
  intro mem
  apply mem_sUnion.mpr
  exists a
  apply And.intro
  apply mem_singleton.mpr
  rfl
  assumption

def Zf.union_comm { a b: α }:
  a ∪ b = b ∪ a := by
  rw [←union_def, ←union_def, pair_comm]

def Zf.inter_comm { a b: α }:
  a ∩ b = b ∩ a := by
  rw [←inter_def, ←inter_def, pair_comm]

def Zf.sub_union { a b: α }:
  a ⊆ b ->
  a ∪ b = b := by
  intro a_sub_b
  apply ext
  intro x
  apply Iff.intro
  intro mem
  cases mem_union.mp mem
  apply a_sub_b
  assumption
  assumption
  intro mem
  apply mem_union.mpr
  apply Or.inr
  assumption

def Zf.sub_inter { a b: α }:
  a ⊆ b ->
  a ∩ b = a := by
  intro a_sub_b
  apply ext
  intro x
  apply Iff.intro
  intro mem
  cases mem_inter.mp mem
  assumption
  intro mem
  apply mem_inter.mpr
  apply And.intro
  assumption
  apply a_sub_b
  assumption

def Iff.not_iff_not { P Q: Prop }:
  (P ↔ Q) -> (¬P ↔ ¬Q) := by
  intro iff
  apply Iff.intro
  intro notp q
  exact notp (iff.mpr q)
  intro notq p
  exact notq (iff.mp p)

def Zf.eq_empty_iff_not_mem { a: α }:
  a = ∅ ↔ ∀x, x ∉ a := by
  apply Iff.intro
  intro empty x
  subst a
  apply not_mem_empty
  intro not_mem
  apply ext
  intro x
  apply Iff.intro
  intro h
  have := not_mem _ h
  contradiction
  intro h
  have := not_mem_empty _ h
  contradiction

def Zf.sdiff_empty_iff_sub { a b: α }:
  a \ b = ∅ ↔ a ⊆ b := by
  apply Iff.intro
  intro sdiff_empty
  intro c c_in_a
  have := not_mem_empty c
  rw [←sdiff_empty] at this
  have := (Iff.not_iff_not (@mem_sdiff α _ a b c)).mp this
  cases lem.not_and.mp this
  contradiction
  apply lem.not_not
  assumption
  intro a_sub_b
  apply eq_empty_iff_not_mem.mpr
  intro x mem
  have ⟨ _, x_notin_b ⟩ := mem_sdiff.mp mem
  apply x_notin_b
  apply a_sub_b
  assumption

def Zf.sub_ext { a b: α } :
  a ⊆ b -> b ⊆ a -> a = b := by
  intro ab ba
  apply ext
  intro x
  apply Iff.intro
  apply ab
  apply ba

def Zf.not_mem_of_sub { a b: α } :
  a ⊆ b -> b ∉ a := by
  intro ab ba
  have := ab _ ba
  exact mem_irrefl _ this

def Zf.sInter_sub_of_mem { a: α }:
  ∀{b}, b ∈ a -> sInter a ⊆ b := by
  intro b mem
  intro c c_in_sinter
  apply (mem_sInter (ne_empty_iff_Nonempty.mpr ⟨ _, mem ⟩)).mp c_in_sinter
  assumption

def Zf.sdiff_inter_comm { a b c: α } :
  (a \ b) ∩ c = (a ∩ c) \ b := by
  apply ext
  intro x
  apply Iff.intro
  · intro mem
    have ⟨ mem, _ ⟩ := mem_inter.mp mem
    have ⟨ _, _ ⟩  := mem_sdiff.mp mem
    apply mem_sdiff.mpr
    apply And.intro
    apply mem_inter.mpr
    apply And.intro
    all_goals assumption
  · intro mem
    have ⟨ mem, _ ⟩ := mem_sdiff.mp mem
    have ⟨ _, _ ⟩ := mem_inter.mp mem
    apply mem_inter.mpr
    apply And.intro
    apply mem_sdiff.mpr
    apply And.intro
    all_goals assumption

def Zf.sub_trans { a b c: α } :
  a ⊆ b -> b ⊆ c -> a ⊆ c := by
  intro ab bc
  intro k  k_in_a
  apply bc
  apply ab
  assumption

def Zf.mem_induction
  { motive: α -> Prop }:
  (mem: ∀x, (∀y ∈ x, motive y) -> (motive x)) ->
  ∀x, motive x := by
  intro mem x
  induction x using (WellFounded.induction Zf.wf)
  assumption
  apply mem
  assumption

def Zf.mem_inductionOn (X: α)
  (motive: α -> Prop) :
  (mem: ∀x ∈ X, (∀y ∈ X, y ∈ x -> motive y) -> (motive x)) ->
  ∀x ∈ X, motive x := by
  intro mem x x_in_X
  induction x using Zf.mem_induction with
  | mem x ih =>
  apply mem
  assumption
  intro y y_in_X y_in_x
  apply ih
  assumption
  assumption

def Zf.exists_min_element (X Y: α):
  Y ⊆ X -> Nonempty Y ->
  ∃x ∈ Y, ∀y ∈ Y, y ∉ x :=by
  intro Y_sub_X nonempty_Y
  apply lem.byContradiction
  intro h
  have := Zf.mem_inductionOn X (fun x => x ∉ Y) (by
    intro x _ ih x_in_Y
    dsimp at ih
    have := not_and.mp <| not_exists.mp h x
    have ⟨ w, h ⟩ := lem.not_forall.mp (this x_in_Y)
    have ⟨ w_in_Y, w_in_x ⟩ := lem.not_imp.mp h
    have := lem.not_not w_in_x
    have := ih w (Y_sub_X _ w_in_Y) this
    contradiction)
  clear h
  dsimp at this
  have : Y = ∅ := by
    apply eq_empty_iff_not_mem.mpr
    intro x x_in_y
    exact this x (Y_sub_X _ x_in_y) x_in_y
  subst Y
  have := ne_empty_iff_Nonempty.mpr nonempty_Y
  contradiction

def   Zf.IsInitialSegmentOf (Y X: α) : Prop :=
  Y ⊆ X ∧ ∀x ∈ X, ∀y ∈ X, x ∈ y -> y ∈ Y -> x ∈ Y

def Zf.exists_successor_of_proper_init_seg (X Y: α):
  Y ⊂ X -> Zf.IsInitialSegmentOf Y X ->
  ∃s ∈ X, s ∉ Y ∧ X ∩ s ⊆ Y := by
  intro Y_ssub_X _
  have := Iff.not_iff_not (@sdiff_empty_iff_sub α _ X Y)
  replace := this.mpr (by
    intro X_sub_Y
    exact Y_ssub_X.right <| Zf.sub_ext Y_ssub_X.left X_sub_Y)
  have ⟨ s, s_in_sdiff, s_min ⟩  := Zf.exists_min_element X (X \ Y) (by
    intro k mem
    exact (mem_sdiff.mp mem).left) (ne_empty_iff_Nonempty.mp this)
  exists s
  apply And.intro
  exact (mem_sdiff.mp s_in_sdiff).left
  apply And.intro
  exact (mem_sdiff.mp s_in_sdiff).right
  intro k k_in_inter
  apply lem.byContradiction
  intro k_notin_Y
  have ⟨ k_in_X, _ ⟩ := mem_inter.mp k_in_inter
  have := s_min k (mem_sdiff.mpr ⟨ k_in_X, k_notin_Y ⟩)
  contradiction

def Zf.mem_of_succ_subset { a b: α } :
  succ a ⊆ b ->
  a ∈ b := by
  intro a_in_b
  apply a_in_b
  apply mem_succ.mpr
  apply Or.inl
  rfl
