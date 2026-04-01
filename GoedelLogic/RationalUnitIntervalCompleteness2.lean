import GoedelLogic.RationalUnitIntervalSoundness
import GoedelLogic.ChainCompleteness
import GoedelLogic.Formula
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Denumerable

-- Attempting to unify the finite and infinite α cases

set_option pp.proofs true

variable {α : Type} [LAlgebra α]
variable {Γ : Set Formula}
variable {F : Set (Quotient (@setoid_formula Γ))}

noncomputable instance linear_order_chain {h : chain α} : LinearOrder α := {
  min_def := λ a b => by
    split_ifs
    · rename_i h1
      simp [h1]
    · rename_i h1
      have h2 : b ≤ a := by
        specialize h a b
        by_contra
        have temp : ¬a ≤ b ∧ ¬b ≤ a := And.intro h1 this
        rw [or_iff_not_and_not] at h
        exact h temp
      simp [h2]
  max_def := λ a b => by
    split_ifs
    · rename_i h1
      simp [h1]
    · rename_i h1
      have h2 : b ≤ a := by
        specialize h a b
        by_contra
        have temp : ¬a ≤ b ∧ ¬b ≤ a := And.intro h1 this
        rw [or_iff_not_and_not] at h
        exact h temp
      simp [h2]
  le_total := h
  toDecidableLE := by
    unfold DecidableLE
    unfold DecidableRel
    intro a b
    by_cases h1 : a ≤ b
    · exact isTrue h1
    · exact isFalse h1 }

def S (N : WithTop ℕ) := {n : ℕ | n ≤ N}

def range (N : WithTop ℕ) (n : ℕ) := {m : S N | m < n}

lemma mem_range (N : WithTop ℕ) (n : ℕ) (x : range N n) : x < n := by
  obtain ⟨x, hx⟩ := x
  simp [range] at hx
  exact hx

lemma y_mem_S (N : WithTop ℕ) (n : S N) (y : ℕ) (hy : y < n) : y ∈ S N := by
  obtain ⟨n, hn⟩ := n
  simp [S] at hn
  simp at hy
  simp [S]
  have hy : (y : WithTop ℕ) ≤ n := by
    rw [le_iff_eq_or_lt]
    simp
    exact Or.inr hy
  exact le_trans hy hn

instance range_equiv (N : WithTop ℕ) (n : S N) : range N n ≃ Fin n := {
  toFun := (fun x => ⟨x, mem_range N n x⟩)
  invFun := (fun y => ⟨⟨y, y_mem_S N n y y.isLt⟩, y.isLt⟩)
}

instance (N : WithTop ℕ) (n : S N) : Finite (range N n) := by
  rw [finite_iff_exists_equiv_fin]
  exists n
  apply Nonempty.intro
  exact range_equiv N n

lemma mem_S (N : WithTop ℕ) (n : ℕ) (hN : n ≤ N) : n ∈ S N := by
  simp [S]
  exact hN

lemma zero_mem_S (N : WithTop ℕ) : 0 ∈ S N := by simp [S]

def h01 {N : WithTop ℕ} {hN : 1 ≤ N} (I : α → S N) : Prop :=
  I Bot.bot = ⟨0, zero_mem_S N⟩  ∧ I Top.top = ⟨1, mem_S N 1 hN⟩

noncomputable def A {N : WithTop ℕ} (I : α → S N) (n : S N) : Finset α :=
  Finset.image I.invFun (@Set.toFinset (S N) (range N n) (Fintype.ofFinite (range N n)))

noncomputable instance decidable_lt {N : WithTop ℕ} (I : α → S N) (n : S N) :
  DecidablePred (fun a => a < I.invFun n) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h : a < I.invFun n
  · exact isTrue h
  · exact isFalse h

noncomputable instance decidable_gt {N : WithTop ℕ} (I : α → S N) (n : S N) :
  DecidablePred (fun a => I.invFun n < a) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h : I.invFun n < a
  · exact isTrue h
  · exact isFalse h

noncomputable def B {N : WithTop ℕ} (I : α → S N) (n : S N) : Finset α :=
  (A I n).filter (fun a => a < I.invFun n)

lemma hB {N : WithTop ℕ} {hN : 2 ≤ N} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} (n : S N) :
  ⟨2, mem_S N 2 hN⟩ ≤ n → (B I n).Nonempty := by
  intro hn
  rw [Finset.Nonempty]
  exists Bot.bot
  rw [B, Finset.mem_filter]
  apply And.intro
  · rw [A, Finset.mem_image]
    exists ⟨0, zero_mem_S N⟩
    apply And.intro
    · simp [range]
      have temp1 : 0 < 1 := by simp
      have temp2 : ⟨1, mem_S N 1 (le_trans one_le_two hN)⟩ < n := Nat.lt_of_succ_le hn
      exact Nat.lt_trans temp1 temp2
    · have temp : I (I.invFun ⟨0, zero_mem_S N⟩) = ⟨0, zero_mem_S N⟩ := by
        apply Function.invFun_eq
        exists Bot.bot
        exact hI2.left
      nth_rewrite 2 [←hI2.left] at temp
      exact bij.left temp
  · by_contra
    rw [not_bot_lt_iff] at this
    have temp1 : I (I.invFun n) = ⟨0, zero_mem_S N⟩ := by
      rw [this]
      exact hI2.left
    have temp2 : I (I.invFun n) = n := by
      apply Function.invFun_eq
      exact bij.right n
    rw [temp1] at temp2
    have temp3 : n ≠ ⟨0, zero_mem_S N⟩ := by
      by_contra
      rw [this] at hn
      rw [← @lt_self_iff_false ℕ]
      exact lt_trans Nat.one_lt_ofNat (Nat.lt_add_one_of_le hn)
    exact temp3 temp2.symm

noncomputable def C {N : WithTop ℕ} (I : α → S N) (n : S N) : Finset α :=
  (A I n).filter (fun a => I.invFun n < a)

lemma hC {N : WithTop ℕ} {hN : 2 ≤ N} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} (n : S N) :
  ⟨2, mem_S N 2 hN⟩ ≤ n → (C I n).Nonempty := by
  intro hn
  rw [Finset.Nonempty]
  exists Top.top
  rw [C, Finset.mem_filter]
  apply And.intro
  · rw [A, Finset.mem_image]
    exists ⟨1, mem_S N 1 (le_trans one_le_two hN)⟩
    apply And.intro
    · simp [range]
      exact Nat.lt_of_succ_le hn
    · have temp : I (I.invFun ⟨1, mem_S N 1 (le_trans one_le_two hN)⟩) = ⟨1, mem_S N 1 (le_trans one_le_two hN)⟩ := by
        apply Function.invFun_eq
        exists Top.top
        exact hI2.right
      nth_rewrite 2 [←hI2.right] at temp
      exact bij.left temp
  · by_contra
    rw [not_lt_top_iff] at this
    have temp1 : I (I.invFun n) = ⟨1, mem_S N 1 (le_trans one_le_two hN)⟩ := by
      rw [this]
      exact hI2.right
    have temp2 : I (I.invFun n) = n := by
      apply Function.invFun_eq
      exact bij.right n
    rw [temp1] at temp2
    have temp3 : n ≠ ⟨1, mem_S N 1 (le_trans one_le_two hN)⟩ := by
      by_contra
      rw [this] at hn
      rw [← @lt_self_iff_false ℕ]
      exact Nat.lt_add_one_of_le hn
    exact temp3 temp2.symm

noncomputable def ai {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} (n : S N) (hn : ⟨2, mem_S N 2 hN⟩ ≤ n) :=
  @Finset.max' α (linear_order_chain (h := hChain)) (B I n) (@hB _ _ _ hN _ bij hI2 n hn)

noncomputable def aj {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} (n : S N) (hn : ⟨2, mem_S N 2 hN⟩ ≤ n) :=
  @Finset.min' α (linear_order_chain (h := hChain)) (C I n) (@hC _ _ _ hN _ bij hI2 n hn)

noncomputable def embed_helper {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} (n : S N) : Q :=
  match n with
  | ⟨0, zero_mem_S⟩ => ⟨0, zero_mem_Q⟩
  | ⟨1, one_mem_S⟩ => ⟨1, one_mem_Q⟩
  | ⟨y + 2, y_succ_succ_mem_S⟩ =>
      mean (@embed_helper hChain _ hN I bij hI2 (I (@ai _ _ hChain _ hN _ bij hI2
            ⟨y + 2, y_succ_succ_mem_S⟩ (Nat.le_add_left 2 y))))
           (@embed_helper hChain _ hN I bij hI2 (I (@aj _ _ hChain _ hN _ bij hI2
            ⟨y + 2, y_succ_succ_mem_S⟩ (Nat.le_add_left 2 y))))
  decreasing_by
    · sorry
    · sorry

noncomputable def embed {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} (a : α) : Q :=
  @embed_helper _ _ hChain _ hN _ bij hI2 (I a)


lemma embed_top {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  @embed _ _ hChain _ hN _ bij hI2 Top.top = Top.top := sorry

lemma embed_bot {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  @embed _ _ hChain _ hN _ bij hI2 Bot.bot = Bot.bot := sorry

lemma embed_helper_order_helper {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  ∀ (k : ℕ), ∀ (m n : S N), m ≤ k → n ≤ k → I.invFun m < I.invFun n →
    @embed_helper _ _ hChain _ hN _ bij hI2 m <
    @embed_helper _ _ hChain _ hN _ bij hI2 n := by sorry

lemma embed_helper_order {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  ∀ (m n : S N), I.invFun m < I.invFun n →
    @embed_helper _ _ hChain _ hN _ bij hI2 m <
    @embed_helper _ _ hChain _ hN _ bij hI2 n := by sorry

lemma embed_order_strict {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  ∀ (a b : α), a < b →
  @embed _ _ hChain _ hN _ bij hI2 a <
  @embed _ _ hChain _ hN _ bij hI2 b := sorry

lemma embed_order {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  ∀ (a b : α), a ≤ b →
  @embed _ _ hChain _ hN _ bij hI2 a ≤
  @embed _ _ hChain _ hN _ bij hI2 b := sorry

lemma my_min_eq_bot {hChain : chain α} {a b : α} : a ⊓ b = Bot.bot → a = Bot.bot ∨ b = Bot.bot := by
  intro h
  cases hChain a b
  · rename_i h1
    have temp : a ⊓ b = a := by simp [h1]
    rw [h] at temp
    simp [temp]
  · rename_i h1
    have temp : a ⊓ b = b := by simp [h1]
    rw [h] at temp
    simp [temp]

lemma embed_inf {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  ∀ (a b : α),
  @embed _ _ hChain _ hN _ bij hI2 (a ⊓ b) =
  @embed _ _ hChain _ hN _ bij hI2 a ⊓
  @embed _ _ hChain _ hN _ bij hI2 b := sorry

lemma embed_sup {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  ∀ (a b : α),
  @embed _ _ hChain _ hN _ bij hI2 (a ⊔ b) =
  @embed _ _ hChain _ hN _ bij hI2 a ⊔
  @embed _ _ hChain _ hN _ bij hI2 b := sorry

lemma chain_himp {hChain : chain α} {a b : α} : ¬ (a ≤ b) → a ⇨ b = b := by
  intro hab
  apply le_antisymm
  · have h1 : (a ⇨ b) ⊓ a = b ⊓ a := himp_inf_self a b
    have h2 : b < a := by
      rw [lt_iff_le_not_ge]
      have hch : a ≤ b ∨ b ≤ a := hChain a b
      have hch : b ≤ a := by
        apply Or.elim hch
        · intro temp
          exfalso
          exact hab temp
        · simp
      exact And.intro hch hab
    have h3 : b ⊓ a = b := by
      simp
      rw [le_iff_eq_or_lt]
      exact Or.inr h2
    have hch : a ⇨ b ≤ a ∨ a ≤ a ⇨ b := hChain (a ⇨ b) a
    have temp : ¬ (a ≤ a ⇨ b) := by
      by_contra
      have haux : a ≤ b := by
        have htemp : a = a ⊓ a := by simp
        rw [htemp]
        rw [←le_himp_iff]
        exact this
      exact hab haux
    have hch : a ⇨ b ≤ a := by
      apply Or.elim hch
      · simp
      · intro temp'
        exfalso
        exact temp temp'
    have h4 : (a ⇨ b) ⊓ a = a ⇨ b := by
      simp only [inf_eq_left]
      exact hch
    rw [h3, h4] at h1
    have h1 : a ⇨ b ≤ b := by
      rw [le_iff_eq_or_lt]
      exact Or.inl h1
    exact h1
  · exact le_himp

lemma embed_to {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  ∀ (a b : α),
  @embed _ _ hChain _ hN _ bij hI2 (a ⇨ b) =
  @embed _ _ hChain _ hN _ bij hI2 a ⇨
  @embed _ _ hChain _ hN _ bij hI2 b := sorry

lemma embed_inj {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  (@embed _ _ hChain _ hN _ bij hI2).Injective := sorry

def Q_homomorphism (f : α → Q) : Prop := f Top.top = Top.top ∧
                f Bot.bot = Bot.bot ∧
                ∀ (a b : α),  (a ≤ b → f a ≤ f b) ∧
                f (a ⊓ b) = f a ⊓ f b ∧
                f (a ⊔ b) = f a ⊔ f b ∧
                f (a ⇨ b) = f a ⇨ f b

lemma embed_homo {hChain : chain α} {N : WithTop ℕ}
  {hN : 2 ≤ N} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := le_trans one_le_two hN) I} :
  Q_homomorphism (@embed _ _ hChain _ hN _ bij hI2) := by
  apply And.intro
  · exact embed_top
  · apply And.intro
    · exact embed_bot
    · intro _ _
      apply And.intro
      · exact @embed_order _ _ _ _ _ _ _ _ _ _
      · apply And.intro
        · exact @embed_inf _ _ _ _ _ _ _ _ _ _
        · apply And.intro
          · exact @embed_sup _ _ _ _ _ _ _ _ _ _
          · exact @embed_to _ _ _ _ _ _ _ _ _ _

noncomputable instance decidable_lt2 (a : α) :
  DecidablePred (fun b => b < a) := by
  unfold DecidablePred
  intro b
  simp
  by_cases h : b < a
  · exact isTrue h
  · exact isFalse h

noncomputable def normal_encoding [Fintype α] (a : α) : ℕ := Finset.card {b : α | b < a}

lemma card_eq [Fintype α] (a b : α) :
  Finset.card {c : α | c < a} = Finset.card {c : α | c < b} → {c : α | c < a} = {c : α | c < b} := by
  contrapose
  intro h
  simp [setOf] at h
  sorry


lemma normal_encoding_bij [Fintype α] : (@normal_encoding α).Bijective := by
  apply And.intro
  · intro a b
    unfold normal_encoding
    intro hab
    sorry
  · sorry

noncomputable def restricted_normal_encoding [Fintype α] (a : α) : Fin (Fintype.card α) :=
  ⟨normal_encoding a,
  by
    unfold normal_encoding
    apply Finset.card_lt_card
    rw [Finset.filter_ssubset]
    exists ⊤
    simp
  ⟩

noncomputable def swapped_restricted_normal_encoding [Fintype α] : α → Fin (Fintype.card α) :=
  (Equiv.swap (restricted_normal_encoding Top.top) 1) ∘ restricted_normal_encoding

noncomputable def finite_encoding [Fintype α] (a : α) : S (Fintype.card α) :=
  ⟨swapped_restricted_normal_encoding a, by simp [mem_S]⟩

lemma embedding {hC : Countable α} : chain α → ∃ (f : α → Q), Q_homomorphism f ∧ Function.Injective f := by
  intro h1
  by_cases hInf : Infinite α
  · have hD : Denumerable α := @Denumerable.ofEncodableOfInfinite α (@Encodable.ofCountable α hC) hInf
    let enum1 := hD.eqv
    let σ2 := Equiv.swap 1 (enum1 ⊤)
    let σ1 := Equiv.swap (σ2 0) (enum1 ⊥)
    let σ := σ1.trans σ2
    let id (n : ℕ) : S ⊤ := ⟨n, mem_S ⊤ n le_top⟩
    let enum2 := id ∘ σ ∘ hD.eqv
    have h01 : enum2 Bot.bot = ⟨0, zero_mem_S ⊤⟩ ∧
               enum2 Top.top = ⟨1, mem_S ⊤ 1 le_top⟩ := by
      unfold enum2
      simp [id, σ]
      apply And.intro
      · unfold σ1
        unfold enum1
        simp
        unfold σ2
        rw [Equiv.swap_apply_def]
        split_ifs
        · rename_i h
          unfold σ1 at h
          rw [Equiv.swap_apply_def] at h
          split_ifs at h
          · exfalso
            assumption
          · exfalso
            rename_i h' _ _
            simp at h'
          · exfalso
            assumption
          · rename_i h'
            exact h'.symm
        · rename_i h h'
          rw [Equiv.swap_apply_def] at h
          split_ifs at h
          · assumption
          · rename_i h'  _ _
            simp at h'
          · rename_i h'  _ _
            simp at h'
          · assumption
          · simp at h
          · rw [Equiv.swap_apply_def] at h'
            split_ifs at h'
            · rename_i h''
              exact h'' h'
        · rename_i h h'
          rw [Equiv.swap_apply_def] at h
          split_ifs at h
          · exfalso
            assumption
          · exfalso
            simp at h
          · exfalso
            rename_i h' _ _
            simp at h'
          · exfalso
            assumption
          · simp at h
          · rw [Equiv.swap_apply_def] at h'
            split_ifs at h'
            · rw [Equiv.swap_apply_def]
              split_ifs
              · simp
      · unfold σ2
        unfold σ1
        unfold enum1
        rw [Equiv.swap_apply_def]
        split_ifs
        · rename_i h
          rw [Equiv.swap_apply_def] at h
          split_ifs at h
          · rename_i h'
            unfold σ2 at h'
            rw [Equiv.swap_apply_def] at h'
            split_ifs at h'
            · exfalso
              assumption
            · exfalso
              rename_i h'' _ _
              simp at h''
            · exfalso
              rename_i h'' _ _
              simp at h''
            · exfalso
              assumption
            · assumption
            · exfalso
              rename_i h''
              unfold enum1 at h''
              exact h'' h'.symm
          · rename_i h'
            have h'' : (⊤ : α) = (⊥ : α) := enum1.injective h'
            simp at h''
          · assumption
        · rename_i h
          rw [Equiv.swap_apply_def] at h
        · rename_i h
          rw [Equiv.swap_apply_def] at h
          split_ifs at h
          · rename_i h'
            unfold σ2 at h'
            rw [Equiv.swap_apply_def] at h'
            split_ifs at h'
            · exfalso
              assumption
            · exfalso
              rename_i h'' _ _
              simp at h''
            · exfalso
              rename_i h'' _ _
              simp at h''
            · exfalso
              assumption
            · rename_i h
              unfold enum1 at h
              rw [h'] at h
              exfalso
              simp at h
            · rename_i h
              unfold enum1 at h
              exfalso
              exact h h'.symm
          · rename_i h'
            have h'' : (⊤ : α) = (⊥ : α) := enum1.injective h'
            simp at h''
          · exfalso
            simp at h
    have bij : (σ ∘ hD.eqv).Bijective := by
      rw [Equiv.comp_bijective]
      apply Equiv.bijective
    have bij : enum2.Bijective := by
      unfold enum2
      apply Function.Bijective.comp
      apply And.intro
      · intro a b
        simp [id]
      · intro b
        exists b
      exact bij
    let f := @embed _ _ h1 ⊤ le_top enum2 bij h01
    have Qhomof : Q_homomorphism f := embed_homo
    have Injf : Function.Injective f := embed_inj
    exists f
  · have hInf : Finite α := by
      rw [←not_infinite_iff_finite]
      exact hInf
    have hInf : Fintype α := Fintype.ofFinite α
    let enum := @finite_encoding α _ _
    have h01 :
      enum Bot.bot = ⟨0, zero_mem_S (Fintype.card α)⟩ ∧
      enum Top.top = ⟨1, mem_S (Fintype.card α) 1 sorry⟩ := sorry
    have bij : enum.Bijective := sorry
    let f := @embed _ _ h1 (Fintype.card α) sorry enum bij h01
    have Qhomof : Q_homomorphism f := embed_homo
    have Injf : Function.Injective f := embed_inj
    exists f

-- f_quot_var will be the valuation that allows us to derive a contradiction in the completeness proof
def f_q_var {hF : filter F} {f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ _) → Q} (v : Var) :=
  f (@filter_quot_var _ _ hF v)

def f_q {hF : filter F} {f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ _) → Q} (ϕ : Formula) :=
  f (@filter_quot _ _ hF ϕ)

lemma f_q_alg_interpretation {hF : filter F} {f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ _) → Q} {hf : Q_homomorphism f}:
  ∀ (ϕ : Formula), @f_q Γ F hF f ϕ = @AlgInterpretation Q _ (f_q_var (f := f)) ϕ := by
  intro ϕ
  induction ϕ with
    | var v => rfl
    | bottom => exact hf.right.left
    | and ψ χ ih1 ih2 =>
        let ψModΓ := @h_lt Γ ψ
        let χModΓ := @h_lt Γ χ
        let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
        let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
        have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ∧∧χ) = and_lt ψModΓ χModΓ := rfl
        have Haux2 : Quotient.mk setoid_filter (and_lt ψModΓ χModΓ) = ψModΓModG ⊓ χModΓModG := rfl
        rw [f_q, filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2, f_q, f_q]
        have h : f (ψModΓModG ⊓ χModΓModG) = f (filter_quot ψ) ⊓ f (filter_quot χ) :=
          (hf.right.right ψModΓModG χModΓModG).right.left
        simp only [setoid_formula.eq_1, h]
    | or ψ χ ih1 ih2 =>
        let ψModΓ := @h_lt Γ ψ
        let χModΓ := @h_lt Γ χ
        let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
        let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
        have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ∨∨χ) = or_lt ψModΓ χModΓ := rfl
        have Haux2 : Quotient.mk setoid_filter (or_lt ψModΓ χModΓ) = ψModΓModG ⊔ χModΓModG := rfl
        rw [f_q, filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2, f_q, f_q]
        have h : f (ψModΓModG ⊔ χModΓModG) = f (filter_quot ψ) ⊔  f (filter_quot χ) :=
          (hf.right.right ψModΓModG χModΓModG).right.right.left
        simp only [setoid_formula.eq_1, h]
    | implication ψ χ ih1 ih2 =>
        let ψModΓ := @h_lt Γ ψ
        let χModΓ := @h_lt Γ χ
        let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
        let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
        have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ⇒χ) = to_lt ψModΓ χModΓ := rfl
        have Haux2 : Quotient.mk setoid_filter (to_lt ψModΓ χModΓ) = ψModΓModG ⇨ χModΓModG := rfl
        rw [f_q, filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2, f_q, f_q]
        have h : f (ψModΓModG ⇨ χModΓModG) = f (filter_quot ψ) ⇨  f (filter_quot χ) :=
          (hf.right.right ψModΓModG χModΓModG).right.right.right
        simp only [setoid_formula.eq_1, h]

-- Gives us a valuation that sets Γ to true, but ϕ to false
lemma rational_contradicting_valuation (ϕ : Formula) : ¬Nonempty (Γ ⊢ ϕ) →
  ∃ (F : Set (Quotient (@setoid_formula Γ))) (hF : prime_filter F)
    (f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ hF.left.left) → Q),
    Q_homomorphism f ∧
    set_true_in_alg_model (@f_q_var _ _ hF.left.left f) Γ ∧
    ¬true_in_alg_model (@f_q_var _ _ hF.left.left f) ϕ := by
  intro notTrueInLTAlgebra
  -- use the same valuation that we used for chains
  have h : ∃ (F : Set (Quotient setoid_formula)) (f : prime_filter F),
  set_true_in_alg_model (@filter_quot_var Γ F f.left.left) Γ ∧
   ¬true_in_alg_model (@filter_quot_var Γ F f.left.left) ϕ := by
    exact @chain_contradicting_valuation Γ ϕ notTrueInLTAlgebra
  obtain ⟨F, hF, hΓ', nhϕ'⟩ := h
  -- take the embedding from A/F into Q
  have embed : ∃ (f : Quotient (setoid_filter (hF := hF.left.left)) → Q),
    Q_homomorphism f ∧ Function.Injective f := @embedding _ _ countable_quotient_algebra (quotient_chain hF)
  obtain ⟨f, hf⟩ := embed
  -- introduce our valuation into Q that will let us derive a contradiction
  let I (v : Var) := f_q_var (f := f) v
  -- show that Γ is true under I
  have hΓ : set_true_in_alg_model I Γ := by
    intros ψ hψ
    specialize hΓ' ψ hψ
    rw [true_in_alg_model, ←filter_quot_interpretation, filter_quot, h_lt] at hΓ'
    rw [true_in_alg_model, ←f_q_alg_interpretation (hf := hf.left), f_q, filter_quot, h_lt, hΓ', hf.left.left]
  -- show that ϕ is not true under I
  have nhϕ : ¬true_in_alg_model I ϕ := by
    by_contra
    rw [true_in_alg_model, ←f_q_alg_interpretation (hf := hf.left), f_q, ←hf.left.left] at this
    rw [true_in_alg_model, ←filter_quot_interpretation] at nhϕ'
    exact nhϕ' (hf.right this)
  exists F, hF, f, hf.left

theorem completeness_rational_unit_interval (ϕ : Formula) : rational_unit_interval_sem_conseq Γ ϕ ↔ Nonempty (Γ ⊢ ϕ) := by
  apply Iff.intro
  · intro unitSemConseq
    by_contra notTrueInLTAlgebra

    -- use the rational_contradicting_valuation lemma
    have h : ∃ (F : Set (Quotient setoid_formula)) (hF : prime_filter F)
      (f : Quotient setoid_filter → Q),
      Q_homomorphism f ∧
      set_true_in_alg_model f_q_var Γ ∧
      ¬true_in_alg_model f_q_var ϕ :=
      rational_contradicting_valuation ϕ notTrueInLTAlgebra
    obtain ⟨F, hF, f, hf, hΓ, nhϕ⟩ := h

    exact nhϕ (unitSemConseq f_q_var hΓ)
  · exact soundness_rational_unit_interval ϕ
