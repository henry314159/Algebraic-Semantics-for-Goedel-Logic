import GoedelLogic.ChainSoundness
import GoedelLogic.LAlgebraCompleteness

variable {α : Type} [LAlgebra α]
variable {Γ : Set Formula}
variable {F : Set α}

-- Define the preorder used to define the equivalence relation
def le (x y : α) : Prop := (x ⇨ y) ∈ F

-- Define the equivalence relation induced on α by F
def equiv_filter (x y : α) := le (F := F) x y ∧ le (F := F) y x

-- Helps to show transitivity of equiv_filter
lemma trans_helper (hF : filter F) {x y z : α} : x ⇨ y ∈ F → y ⇨ z ∈ F → x ⇨ z ∈ F := by
  intros h1 h2
  exact hF.right.right _ _ (hF.right.left _ _ h1 h2) (himp_triangle _ _ _)

-- Shows that equiv_filter is indeed an equivalence relation
instance setoid_filter {hF : filter F} : Setoid α :=
  { r := equiv_filter,
    iseqv := ⟨
      λ _ => by
        simp [equiv_filter, le]
        exact top_mem_filter _ hF,
      λ _ => by
        apply And.symm
        assumption,
      λ H12 H23 => ⟨trans_helper hF H12.left H23.left, trans_helper hF H23.right H12.right⟩
    ⟩
  }

-- LAlgebra.or_filter x y is [x ⊔ y]
def LAlgebra.or_filter {hF : filter F} (x y : α) := Quotient.mk (setoid_filter (hF := hF)) (x ⊔ y)

-- x~x',y~y'=>[x ⊔ y]=[x' ⊔ y']
lemma or_filter_preserves_equiv {hF : filter F} (x y x' y' : α) :
  equiv_filter (F := F) x x' → equiv_filter (F := F) y y' →
  (LAlgebra.or_filter (hF := hF) x y = LAlgebra.or_filter x' y') := by
  simp [equiv_filter]
  intros h1 h2 h3 h4
  apply Quotient.sound
  apply And.intro
  · have h5 : ((x ⇨ x') ⊓ (y ⇨ y')) ≤ (x ⊔ y ⇨ x' ⊔ y') := by
      rw [le_himp_iff, inf_sup_left, inf_right_comm, inf_assoc, inf_left_comm, ← inf_assoc, inf_himp,
        sup_comm, inf_right_comm, inf_assoc, inf_himp, ← inf_assoc]
      simp
      have h6 : x ⊓ x' ⊓ (y ⇨ y') ≤ x' := by
        rw [inf_right_comm]
        exact inf_le_right
      have h7 : x' ≤ x' ⊔ y' := by simp
      exact le_trans h6 h7
    have h6 : (x ⇨ x') ⊓ (y ⇨ y') ∈ F := hF.right.left _ _ h1 h3
    exact hF.right.right _ _ h6 h5
  · have h5 : ((x' ⇨ x) ⊓ (y' ⇨ y)) ≤ (x' ⊔ y' ⇨ x ⊔ y) := by
      rw [le_himp_iff, inf_sup_left, inf_right_comm, inf_assoc, inf_left_comm, ← inf_assoc, inf_himp,
      sup_comm, inf_right_comm, inf_assoc, inf_himp, ← inf_assoc]
      simp
      have h6 : x' ⊓ x ⊓ (y' ⇨ y) ≤ x := by
        rw [inf_right_comm]
        exact inf_le_right
      have h7 : x ≤ x ⊔ y := by simp
      exact le_trans h6 h7
    have h6 : (x' ⇨ x) ⊓ (y' ⇨ y) ∈ F := hF.right.left _ _ h2 h4
    exact hF.right.right _ _ h6 h5

-- define or for quotient algebra
def or_filter {hF : filter F} (x y : Quotient (setoid_filter (hF := hF))) : Quotient (setoid_filter (hF := hF)) :=
  Quotient.lift₂ (s₁ := setoid_filter) (s₂ := setoid_filter) LAlgebra.or_filter or_filter_preserves_equiv x y

-- LAlgebra.and_filter x y is [x ⊓ y]
def LAlgebra.and_filter {hF : filter F} (x y : α) := Quotient.mk (setoid_filter (hF := hF)) (x ⊓ y)

-- x~x',y~y'=>[x ⊓ y]=[x' ⊓ y']
lemma and_filter_preserves_equiv {hF : filter F} (x y x' y' : α) : equiv_filter (F := F) x x' → equiv_filter (F := F) y y' →
  (LAlgebra.and_filter (hF := hF) x y = LAlgebra.and_filter x' y') := by
  simp only [equiv_filter, and_imp]
  intros h1 h2 h3 h4
  apply Quotient.sound
  apply And.intro
  · have h5 : (x ⇨ x') ⊓ (y ⇨ y') ≤ (x ⊓ y) ⇨ (x' ⊓ y') := by
      rw [le_himp_iff, le_inf_iff, inf_left_comm, inf_assoc, himp_inf_self, ← inf_assoc, inf_himp]
      apply And.intro
      · rw [inf_assoc, inf_comm, inf_assoc]
        exact inf_le_left
      · rw [inf_comm, inf_assoc]
        exact inf_le_left
    have h6 : (x ⇨ x') ⊓ (y ⇨ y') ∈ F := hF.right.left _ _ h1 h3
    exact hF.right.right _ _ h6 h5
  · have h5 : (x' ⇨ x) ⊓ (y' ⇨ y) ≤ (x' ⊓ y') ⇨ (x ⊓ y) := by
      rw [le_himp_iff, le_inf_iff, inf_left_comm, inf_assoc, himp_inf_self, ← inf_assoc, inf_himp]
      apply And.intro
      · rw [inf_assoc, inf_comm, inf_assoc]
        exact inf_le_left
      · rw [inf_comm, inf_assoc]
        exact inf_le_left
    have h6 : (x' ⇨ x) ⊓ (y' ⇨ y) ∈ F := hF.right.left _ _ h2 h4
    exact hF.right.right _ _ h6 h5

-- Define and for quotient algebra
def and_filter {hF : filter F} (x y : Quotient (setoid_filter (hF := hF))) : Quotient (setoid_filter (hF := hF)) :=
  Quotient.lift₂ (s₁ := setoid_filter) (s₂ := setoid_filter) LAlgebra.and_filter and_filter_preserves_equiv x y

-- LAlgebra.and_filter x y is [x ⇨ y]
def LAlgebra.to_filter {hF : filter F} (x y : α) := Quotient.mk (setoid_filter (hF := hF)) (x ⇨ y)

-- x~x',y~y'=>[x ⇨ y]=[x' ⇨ y']
lemma to_filter_preserves_equiv {hF : filter F} (x y x' y' : α) : equiv_filter (F := F) x x' → equiv_filter (F := F) y y' →
  (LAlgebra.to_filter (hF := hF) x y = LAlgebra.to_filter x' y') := by
  simp only [equiv_filter, and_imp]
  intros h1 h2 h3 h4
  apply Quotient.sound
  apply And.intro
  · have h5 : (x' ⇨ x) ⊓ (y ⇨ y') ≤ (x ⇨ y) ⇨ (x' ⇨ y') := by
      rw [le_himp_iff, inf_right_comm]
      have h6 : (x' ⇨ y) ⊓ (y ⇨ y') ≤ x' ⇨ y' := himp_triangle _ _ _
      have h7 : (x' ⇨ x) ⊓ (x ⇨ y) ≤ x' ⇨ y := himp_triangle _ _ _
      have h8 : (x' ⇨ x) ⊓ (x ⇨ y) ⊓ (y ⇨ y') ≤ (x' ⇨ y) ⊓ (y ⇨ y') := by
        exact inf_le_inf_right _ h7
      exact le_trans h8 h6
    have h9 : (x' ⇨ x) ⊓ (y ⇨ y') ∈ F := hF.right.left _ _ h2 h3
    exact hF.right.right _ _ h9 h5
  · have h5 : (x ⇨ x') ⊓ (y' ⇨ y) ≤ (x' ⇨ y') ⇨ (x ⇨ y) := by
      rw [le_himp_iff, inf_right_comm]
      have h6 : (x ⇨ y') ⊓ (y' ⇨ y) ≤ x ⇨ y := himp_triangle _ _ _
      have h7 : (x ⇨ x') ⊓ (x' ⇨ y') ≤ x ⇨ y' := himp_triangle _ _ _
      have h8 : (x ⇨ x') ⊓ (x' ⇨ y') ⊓ (y' ⇨ y) ≤ (x ⇨ y') ⊓ (y' ⇨ y) := by
        exact inf_le_inf_right _ h7
      exact le_trans h8 h6
    have h9 : (x ⇨ x') ⊓ (y' ⇨ y) ∈ F := hF.right.left _ _ h1 h4
    exact hF.right.right _ _ h9 h5

-- Define ⇨ for quotient algebra
def to_filter {hF : filter F} (x y : Quotient (setoid_filter (hF := hF))) : Quotient (setoid_filter (hF := hF)) :=
  Quotient.lift₂ (s₁ := setoid_filter) (s₂ := setoid_filter) LAlgebra.to_filter to_filter_preserves_equiv x y

-- x~x', y~y' => ((x ⇨ y) ∈ F iff (x' ⇨ y') ∈ F)
lemma le_preserves_equiv_filter {hF : filter F} (x y x' y' : α) :
  equiv_filter (F := F) x x' → equiv_filter (F := F) y y' → le (F := F) x y = le (F := F) x' y' := by
  intros hx hy
  rw [eq_iff_iff]
  apply Iff.intro
  · intro h1
    have h2 : (x' ⇨ x) ⊓ (x ⇨ y) ⊓ (y ⇨ y') ≤ x' ⇨ y' := by
      rw [le_himp_iff, inf_comm, ← inf_assoc, ← inf_assoc]
      simp only [inf_assoc, inf_himp]
      rw [← inf_assoc, ← inf_assoc]
      exact inf_le_right
    have h3 : (x' ⇨ x) ⊓ (x ⇨ y) ∈ F := hF.right.left _ _ hx.right h1
    have h4 : (x' ⇨ x) ⊓ (x ⇨ y) ⊓ (y ⇨ y') ∈ F := hF.right.left _ _ h3 hy.left
    exact hF.right.right _ _ h4 h2
  · intro h1
    have h2 : (x ⇨ x') ⊓ (x' ⇨ y') ⊓ (y' ⇨ y) ≤ x ⇨ y := by
      rw [le_himp_iff, inf_comm, ← inf_assoc, ← inf_assoc]
      simp only [inf_assoc, inf_himp]
      rw [← inf_assoc, ← inf_assoc]
      exact inf_le_right
    have h3 : (x ⇨ x') ⊓ (x' ⇨ y') ∈ F := hF.right.left _ _ hx.left h1
    have h4 : (x ⇨ x') ⊓ (x' ⇨ y') ⊓ (y' ⇨ y) ∈ F := hF.right.left _ _ h3 hy.right
    exact hF.right.right _ _ h4 h2

-- Define le for the quotient algebra, using well-definedness from above
def le_filter {hF : filter F} (x y : Quotient (setoid_filter (hF := hF))) : Prop :=
  Quotient.lift₂ (s₁ := setoid_filter) (s₂ := setoid_filter) le (le_preserves_equiv_filter (hF := hF)) x y

-- These results help prove that if A is an LAlgebra and F a filter, A/F is an LAlgebra
lemma my_le_refl {hF : filter F} : ∀ (a : α), @le _ _ F a a := by
  intro
  simp [le]
  exact top_mem_filter (Hfilter := hF)

lemma my_le_trans {hF : filter F} : ∀ (a b c : α), @le _ _ F a b → @le _ _ F b c → @le _ _ F a c := by
  intro _ _ _ hab hbc
  unfold le at *
  exact trans_helper hF hab hbc

lemma my_le_sup_left {hF : filter F} : ∀ (a b : α), @le _ _ F a (a ⊔ b) := by
  intro a b
  unfold le
  have h : a ⇨ a ⊔ b = Top.top := by simp
  rw [h]
  exact top_mem_filter (Hfilter := hF)

lemma my_le_sup_right {hF : filter F} : ∀ (a b : α), @le _ _ F b (a ⊔ b) := by
  intro a b
  have h : b ⇨ a ⊔ b = Top.top := by simp
  rw [le, h]
  exact top_mem_filter (Hfilter := hF)

lemma my_sup_le {hF : filter F} : ∀ (a b c : α), @le _ _ F a c → @le _ _ F b c → @le _ _ F (a ⊔ b) c := by
  intro _ _ _ hac hbc
  unfold le at *
  rw [sup_himp_distrib]
  exact hF.right.left _ _ hac hbc

lemma my_inf_le_left {hF : filter F} : ∀ (a b : α), @le _ _ F (a ⊓ b) a := by
  intro a b
  have h : a ⊓ b ⇨ a = Top.top := by simp
  rw [le, h]
  exact top_mem_filter (Hfilter := hF)

lemma my_inf_le_right {hF : filter F} : ∀ (a b : α), @le _ _ F (a ⊓ b) b := by
  intro a b
  unfold le
  have h : a ⊓ b ⇨ b = Top.top := by simp
  rw [h]
  exact top_mem_filter (Hfilter := hF)

lemma my_le_inf {hF : filter F} : ∀ (a b c : α), @le _ _ F a b → @le _ _ F a c → @le _ _ F a (b ⊓ c) := by
  intro _ _ _ hab hac
  unfold le at *
  rw [himp_inf_distrib]
  exact hF.right.left _ _ hab hac

lemma my_le_himp_iff : ∀ (a b c : α), @le _ _ F a (b ⇨ c) ↔ @le _ _ F (a ⊓ b) c := by
  intro _ _ _
  unfold le
  apply Iff.intro
  · intro habc
    simp only [← himp_himp, habc]
  · intro habc
    simp only [himp_himp, habc]

lemma my_le_top {hF : filter F} : ∀ (a : α), @le _ _ F a ⊤ := by
  intro
  simp [le]
  exact top_mem_filter (Hfilter := hF)

lemma my_bot_le {hF : filter F} : ∀ (a : α), @le α _ F ⊥ a := by
  intro
  simp [le]
  exact top_mem_filter (Hfilter := hF)

-- Prove that the quotient algebra is an LAlgebra
instance quotient_algebra {hF : filter F} : LAlgebra (Quotient (setoid_filter (hF := hF))) :=
  { le := le_filter
    le_refl := λ q => by
      induction q using Quotient.ind
      exact my_le_refl (hF := hF) _
    le_trans := λ q1 q2 q3 H12 H23 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      exact my_le_trans (hF := hF) _ _ _ H12 H23
    le_antisymm := λ q1 q2 H12 H21 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      apply Quotient.sound
      apply And.intro
      · exact H12
      · exact H21
    sup := or_filter
    le_sup_left := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      exact my_le_sup_left (hF := hF) _ _
    le_sup_right := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      exact my_le_sup_right (hF := hF) _ _
    sup_le := λ q1 q2 q3 H13 H23 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      exact my_sup_le (hF := hF) _ _ _ H13 H23
    inf := and_filter
    inf_le_left := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      exact my_inf_le_left (hF := hF) _ _
    inf_le_right := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      exact my_inf_le_right (hF := hF) _ _
    le_inf := λ q1 q2 q3 H13 H23 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      exact my_le_inf (hF := hF) _ _ _ H13 H23
    top := Quotient.mk _ ⊤
    le_top := λ q => by
      induction q using Quotient.ind
      exact my_le_top (hF := hF) _
    himp := to_filter
    le_himp_iff := λ q1 q2 q3 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      induction q3 using Quotient.ind
      exact my_le_himp_iff _ _ _
    bot := Quotient.mk _ ⊥
    bot_le := λ q => by
      induction q using Quotient.ind
      exact my_bot_le (hF := hF) _
    compl := λ q => to_filter q (Quotient.mk _ _)
    himp_bot := λ q => by rfl
    l_axiom := λ q1 q2 => by
      induction q1 using Quotient.ind
      induction q2 using Quotient.ind
      apply Quotient.sound
      simp [HasEquiv.Equiv, setoid_filter, LAlgebra.l_axiom, equiv_filter, le]
      exact top_mem_filter (Hfilter := hF)
    }

instance countable_quotient_algebra {Γ : Set Formula} {F : Set (Quotient (@setoid_formula Γ))} {hF : filter F} : Countable (Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ hF)) := by
  apply @Function.Surjective.countable (Quotient (@setoid_formula Γ))
                                       (Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ hF))
                                       countable_lt
                                       (Quotient.mk setoid_filter)
                                       Quotient.mk_surjective

-- lemma that says if F is a prime filter and A an LAlgebra, then A/F is a chain
lemma quotient_chain {hF : filter F}: prime_filter F → chain (Quotient (setoid_filter (hF := hF))) := by
  intro p a b
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i x y
  have h1 : (x ⇨ y) ⊔ (y ⇨ x) ∈ F := by
    rw [LAlgebra.l_axiom]
    exact top_mem_filter (Hfilter := hF)
  exact p.right _ _ h1

--def ideal (I : Set α) := Set.Nonempty I ∧ ∀ (x y : α), x ∈ I → y ∈ I → x ⊔ y ∈ I

variable {F : Set (Quotient (@setoid_formula Γ))}
variable {hF : filter F}

-- filter_quot_var is the valuation that will allow us to derive a contradiction in the completeness proof
def filter_quot_var (v : Var) : Quotient (setoid_filter (α := Quotient setoid_formula) (hF := hF)) :=
  Quotient.mk setoid_filter (h_lt_var v)

def filter_quot (ϕ : Formula) : Quotient (setoid_filter (α := Quotient setoid_formula) (hF := hF)) :=
  Quotient.mk setoid_filter (h_lt ϕ)

lemma filter_quot_interpretation :
  ∀ (ϕ : Formula),  filter_quot ϕ = @AlgInterpretation (Quotient (setoid_filter (α := Quotient (@setoid_formula Γ)) (hF := hF))) _ filter_quot_var ϕ := by
    intro ϕ
    induction ϕ with
      | var v => rfl
      | bottom => rw [filter_quot, AlgInterpretation, h_lt]
                  rfl
      | and ψ χ ih1 ih2 => let ψModΓ := @h_lt Γ ψ
                           let χModΓ := @h_lt Γ χ
                           let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
                           let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
                           have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ∧∧χ) = and_lt ψModΓ χModΓ := by rfl
                           have Haux2 : Quotient.mk setoid_filter (and_lt ψModΓ χModΓ) = and_filter ψModΓModG χModΓModG := by rfl
                           rw [filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2]
                           rfl
      | or ψ χ ih1 ih2 => let ψModΓ := @h_lt Γ ψ
                          let χModΓ := @h_lt Γ χ
                          let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
                          let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
                          have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ∨∨χ) = or_lt ψModΓ χModΓ := by rfl
                          have Haux2 : Quotient.mk setoid_filter (or_lt ψModΓ χModΓ) = or_filter ψModΓModG χModΓModG := by rfl
                          rw [filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2]
                          rfl
      | implication ψ χ ih1 ih2 => let ψModΓ := @h_lt Γ ψ
                                   let χModΓ := @h_lt Γ χ
                                   let ψModΓModG := Quotient.mk (setoid_filter (hF := hF)) ψModΓ
                                   let χModΓModG := Quotient.mk (setoid_filter (hF := hF)) χModΓ
                                   have Haux1 : Quotient.mk (@setoid_formula Γ) (ψ⇒χ) = to_lt ψModΓ χModΓ := by rfl
                                   have Haux2 : Quotient.mk setoid_filter (to_lt ψModΓ χModΓ) = to_filter ψModΓModG χModΓModG := by rfl
                                   rw [filter_quot, AlgInterpretation, h_lt, Haux1, Haux2, <-ih1, <-ih2]
                                   rfl

-- Lemma that says there exists filter F such that filter_quot_var sets Γ to true, but sets ϕ to false
lemma chain_contradicting_valuation (ϕ : Formula) : ¬Nonempty (Γ ⊢ ϕ) →
  ∃ (F : Set (Quotient (@setoid_formula Γ))) (hF : prime_filter F),
    set_true_in_alg_model (@filter_quot_var Γ F hF.left.left) Γ ∧
    ¬true_in_alg_model (@filter_quot_var Γ F hF.left.left) ϕ := by

  intro notTrueInLTAlgebra
  rw [←true_in_lt] at notTrueInLTAlgebra
  let ϕModΓ := @h_lt Γ ϕ

  -- hNotTop means that we can find a filter F that separates top and ϕ
  have hNotTop : ϕModΓ ≠ Top.top := by
    simp [true_in_alg_model, ← h_lt_interpretation ϕ, h_lt] at notTrueInLTAlgebra
    exact notTrueInLTAlgebra

  -- there exists a filter F that separates top and ϕ
  have hF : ∃F, prime_filter F ∧ ϕModΓ ∉ F := super_prime_filter_cor1 ϕModΓ hNotTop
  obtain ⟨F, hF1, hF2⟩ := hF
  let valuation := @filter_quot_var _ _ hF1.left.left

  -- valuation sets all ψ ∈ Γ to true
  have hΓ : set_true_in_alg_model valuation Γ := by
    -- this is true by construction
    intros ψ hψ
    have hψ : Quotient.mk (@setoid_formula Γ) ψ = Top.top := by
      rw [← equiv_top]
      apply Nonempty.intro
      exact Proof.premise hψ
    rw [true_in_alg_model, ←filter_quot_interpretation, filter_quot, h_lt]
    apply Quotient.sound
    simp [HasEquiv.Equiv, setoid_filter, hψ, equiv_filter, le]
    exact @top_mem_filter _ _ _ hF1.left.left

  -- valuation does not set ϕ to true
  have nhϕ : ¬true_in_alg_model valuation ϕ := by
    -- it is sufficient to show that ϕModΓModF ≠ ⊤
    rw [true_in_alg_model, ←filter_quot_interpretation]
    -- assume for contradiction that ϕModΓModF = ⊤
    by_contra
    -- we then have ϕModΓ ~ ⊤
    have ϕEquivTop : equiv_filter (Quotient.mk _ ϕ) Top.top := Quotient.exact this
    -- we can now show that ϕ ∈ F, which is a contradiction
    have ϕInF : ϕModΓ ∈ F := by
      simp [equiv_filter, le] at ϕEquivTop
      exact ϕEquivTop.right
    exact hF2 ϕInF
  exists F, hF1

theorem completeness_chains (ϕ : Formula) : chain_sem_conseq Γ ϕ ↔ Nonempty (Γ ⊢ ϕ) :=
  by
    apply Iff.intro
    · intro chainSemConseq
      by_contra notTrueInLTAlgebra

      -- use the lemma chain_contradicting_valuation
      have h : ∃ (F : Set (Quotient setoid_formula)) (hF : prime_filter F),
        set_true_in_alg_model filter_quot_var Γ ∧
        ¬true_in_alg_model filter_quot_var ϕ :=
        chain_contradicting_valuation ϕ notTrueInLTAlgebra
      obtain ⟨F, hF, hΓ, nhϕ⟩ := h
      let valuation := @filter_quot_var _ _ hF.left.left

      -- the assumption that Γ ⊨ ϕ is specialised to LT/F and valuation
      specialize chainSemConseq (Quotient setoid_filter) valuation

      -- show that, under the assumption Γ ⊨ ϕ, we have ϕ is true under valuation
      have hϕ : true_in_alg_model valuation ϕ := by
        apply chainSemConseq
        exact And.intro (quotient_chain hF) hΓ
      exact nhϕ hϕ
    · exact soundness_chains ϕ
