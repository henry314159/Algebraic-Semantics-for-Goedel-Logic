import GoedelLogic.RationalUnitIntervalSoundness
import GoedelLogic.ChainCompleteness
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max

set_option pp.proofs true

variable {α : Type} [LAlgebra α]
variable {Γ : Set Formula}
variable {F : Set (Quotient (@setoid_formula Γ))}

-- Show that a chain is a linear order
noncomputable instance lo {h : chain α} : LinearOrder α := {
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

-- Define what it means for a function f : α → Q to be a homomorphism
def Qhomomorphism (f : α → Q) : Prop := f Top.top = Top.top ∧
                f Bot.bot = Bot.bot ∧
                ∀ (a b : α),  (a ≤ b → f a ≤ f b) ∧
                f (a ⊓ b) = f a ⊓ f b ∧
                f (a ⊔ b) = f a ⊔ f b ∧
                f (a ⇨ b) = f a ⇨ f b

-- We need to enumerate the values in α such that ⊥ and ⊤ come first
def I01 (I : ℕ → α) : Prop := I 0 = Bot.bot ∧ I 1 = Top.top

noncomputable def A {I : ℕ → α} (n : ℕ) : Finset α :=
  Finset.image I (Finset.range n)

noncomputable instance decidable1 {I : ℕ → α} (n : ℕ) :
  DecidablePred (fun a => a < I n) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h1 : a < I n
  · exact isTrue h1
  · exact isFalse h1

noncomputable instance decidable2 {I : ℕ → α} (n : ℕ) :
  DecidablePred (fun a => I n < a) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h1 : I n < a
  · exact isTrue h1
  · exact isFalse h1

noncomputable def B {I : ℕ → α} (n : ℕ) : Finset α :=
  @(@A α I n).filter α (fun a => a < I n) (decidable1 n)

lemma hB {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) : 2 ≤ n → (@B α _ I n).Nonempty := by
  intro hn
  rw [Finset.Nonempty]
  exists Bot.bot
  rw [B , Finset.mem_filter]
  apply And.intro
  · rw [A, Finset.mem_image]
    exists 0
    apply And.intro
    · rw [Finset.mem_range]
      have temp1 : 0 < 1 := by simp
      have temp2 : 1 < n := Nat.lt_of_succ_le hn
      exact Nat.lt_trans temp1 temp2
    · exact hI2.left
  · have inj : Function.Injective I := hI1.left
    unfold Function.Injective at inj
    let inj := @inj n 0
    have inj : n ≠ 0 → I n ≠ Bot.bot := by
      contrapose
      rw [←hI2.left]
      exact inj
    have temp : n ≠ 0 := by sorry
    have h3 : I n ≠ Bot.bot := by exact inj temp
    by_contra
    rw [not_bot_lt_iff] at this
    exact h3 this

noncomputable def C {I : ℕ → α} (n : ℕ) : Finset α :=
  @(@A α I n).filter α (fun a => I n < a) (decidable2 n)

lemma hC {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) : 2 ≤ n → (@C α _ I n).Nonempty := by
  intro hn
  rw [Finset.Nonempty]
  exists Top.top
  rw [C, Finset.mem_filter]
  apply And.intro
  · rw [A, Finset.mem_image]
    exists 1
    apply And.intro
    · rw [Finset.mem_range]
      exact Nat.lt_of_succ_le hn
    · exact hI2.right
  · have inj : Function.Injective I := hI1.left
    unfold Function.Injective at inj
    let inj := @inj n 1
    have inj : n ≠ 1 → I n ≠ Top.top := by
      contrapose
      rw [←hI2.right]
      exact inj
    have temp : n ≠ 1 := by sorry
    have h3 : I n ≠ Top.top := inj temp
    by_contra
    rw [not_lt_top_iff] at this
    exact h3 this

noncomputable def ai {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) (hn : 2 ≤ n) : α :=
  @Finset.max' α (@lo α _ hChain) (@B α _ I n) (@hB α _ I hI1 hI2 n hn)

noncomputable def aj {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) (hn : 2 ≤ n) : α :=
  @Finset.min' α (@lo α _ hChain) (@C α _ I n) (@hC α _ I hI1 hI2 n hn)

-- Tidy up this definition, use some lemmas to make it shorter
-- Defines the embedding assuming we have a suitable enumeration of the elements in the chain
noncomputable def embedHelper {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) : Q :=
  match n with
  | 0 => ⟨0, zero_memQ⟩
  | 1 => ⟨1, one_memQ⟩
  | Nat.succ (Nat.succ y) =>
      mean (@embedHelper hChain I hI1 hI2 (Function.invFun I (@ai α _ hChain _ hI1 hI2 (Nat.succ (Nat.succ y)) (Nat.le_add_left 2 y))))
           (@embedHelper hChain I hI1 hI2 (Function.invFun I (@aj α _ hChain _ hI1 hI2 (Nat.succ (Nat.succ y)) (Nat.le_add_left 2 y))))
  decreasing_by
    · sorry
    · sorry
    /-have h3 : ai = {a ∈ Finset.image I (Finset.range x) | a < I x}.max' hB := by
      sorry
    rw [←h3]
    let p (a : α) : Prop := a < I x
    have h4 : ai ∈ B := by exact @Finset.max'_mem _ _ _ _
    have h5 : ai ∈ A ∧ p ai := by
      rw [←Finset.mem_filter]
      exact h4
    have h5 : ai ∈ A := by exact h5.left
    rw [Finset.mem_image] at h5
    obtain ⟨a, ha1, ha2⟩ := h5
    have h6 : Function.invFun I ai = a := by
      have h7 : Function.invFun I ∘ I = id := by exact @Function.invFun_comp _ _ _ _ hI1.left
      rw [←ha2]
      have h8 : (Function.invFun I ∘ I) a = a := by
        rw [h7]
        exact id_eq a
      exact h8
    rw [h6]
    have ha2 : a < y.succ.succ := by
      rw [Finset.mem_range] at ha1
      simp
      rw [←hx]
      exact ha1
    exact ha2
    have h3 : aj = {a ∈ Finset.image I (Finset.range x) | I x < a}.min' hC := by rfl
    rw [←h3]
    let p (a : α) : Prop := I x < a
    have h4 : aj ∈ C := by exact @Finset.min'_mem _ _ _ _
    have h5 : aj ∈ A ∧ p aj := by
      rw [←Finset.mem_filter]
      exact h4
    have h5 : aj ∈ A := by exact h5.left
    rw [Finset.mem_image] at h5
    obtain ⟨a, ha1, ha2⟩ := h5
    have h6 : Function.invFun I aj = a := by
      have h7 : Function.invFun I ∘ I = id := by exact @Function.invFun_comp _ _ _ _ hI1.left
      rw [←ha2]
      have h8 : (Function.invFun I ∘ I) a = a := by
        rw [h7]
        exact id_eq a
      exact h8
    rw [h6]
    rw [←Finset.mem_range]
    exact ha1-/

-- Embed is our monomorphism (a.k.a. embedding, or injective homomorphism) A/F → [0,1]_ℚ
noncomputable def embed {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (a : α) : Q :=
  @embedHelper _ _ hChain _ hI1 hI2 (Function.invFun I a)

lemma embedTop {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : @embed α _ hChain I hI1 hI2 Top.top = Top.top := by
  have h_inv : Function.invFun I Top.top = 1 := by
    rw [←hI2.right]
    have h1 : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
    have h2 : (Function.invFun I ∘ I) 1 = 1 := by
      rw [h1]
      exact id_eq 1
    exact h2
  rw [embed, h_inv, embedHelper]
  rfl

lemma embedBot {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : @embed α _ hChain I hI1 hI2 Bot.bot = Bot.bot := by
  have h_inv : Function.invFun I Bot.bot = 0 := by
    rw [←hI2.left]
    have h1 : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
    have h2 : (Function.invFun I ∘ I) 0 = 0 := by
      rw [h1]
      exact id_eq 0
    exact h2
  rw [embed, h_inv, embedHelper]
  rfl

lemma mean_le (a : Q) (b : Q) (c : Q) : a ≤ b → a ≤ c → a ≤ mean b c := by sorry

lemma embedOrderHelper {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I}:
  ∀ (n m : ℕ), I n ≤ I m → @embedHelper _ _ hChain _ hI1 hI2 n ≤ @embedHelper _ _ hChain _ hI1 hI2 m := by
  intro n m
  apply @Nat.strong_induction_on _ m
  intro k ih hnm
  unfold embedHelper
  split
  · exact bot_le
  · rw [hI2.right] at hnm
    simp at hnm
    have h : k = 1 := by
      rw [←hI2.right] at hnm
      have temp : Function.Injective I := hI1.left
      let temp := @temp k 1
      exact temp hnm
    simp [h]
  · split
    · exfalso
      rw [hI2.left] at hnm
      simp only [le_bot_iff] at hnm
      rename_i y _
      rw [←hI2.left] at hnm
      have hy1 : y.succ.succ = 0 := hI1.left hnm
      have hy1 : 0 = y.succ.succ := by rw [hy1]
      have hy2 : 0 ≠ y.succ.succ := by simp
      exact hy2 hy1
    · exact le_top
    · rename_i n1 y1 n2 y2
      let ai1 := @ai α _ hChain _ hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1)
      let aj1 := @aj α _ hChain _ hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1)
      let ai2 := @ai α _ hChain _ hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2)
      let aj2 := @aj α _ hChain _ hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2)
      have temp1 : @embedHelper _ _ hChain _ hI1 hI2 (y1.succ.succ) = mean (@embedHelper α _ hChain I hI1 hI2 (Function.invFun I ai1))
                (@embedHelper α _ hChain I hI1 hI2 (Function.invFun I aj1)) := by rw [embedHelper]
      have temp2 : @embedHelper _ _ hChain _ hI1 hI2 (y2.succ.succ) = mean (@embedHelper α _ hChain I hI1 hI2 (Function.invFun I ai2))
                (@embedHelper α _ hChain I hI1 hI2 (Function.invFun I aj2)) := by rw [embedHelper]
      simp only [ai1, aj1, ai2, aj2, ←temp1, ←temp2]
      rw [le_iff_eq_or_lt]
      by_cases h : I y1.succ.succ = I y2.succ.succ
      · apply Or.intro_left
        rw [hI1.left h]
      · have h : I y1.succ.succ < I y2.succ.succ := by
          rw [lt_iff_le_and_ne]
          apply And.intro
          · exact hnm
          · exact h
        by_cases h' : y1.succ.succ < y2.succ.succ
        · have h1 : I y1.succ.succ ≤ ai2 := by -- since ai2 is the largest less than I y2.succ.succ
            have temp : I y1.succ.succ ∈ @B _ _ I y2.succ.succ := by
              unfold B
              rw [@Finset.mem_filter α (fun a => a < I y2.succ.succ) (@decidable1 α _ I y2.succ.succ) (@A α I y2.succ.succ) (I y1.succ.succ)]
              apply And.intro
              · unfold A
                rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) (I y1.succ.succ)]
                exists y1.succ.succ
                apply And.intro
                · rw [Finset.mem_range]
                  exact h'
                · rfl
              · exact h
            exact @Finset.le_max' α (@lo α _ hChain) (@B _ _ I y2.succ.succ) (I y1.succ.succ) temp
          have h1 : I y1.succ.succ ≤ I (Function.invFun I ai2) := by
            have temp : I (Function.invFun I ai2) = ai2 := by
              apply Function.invFun_eq
              have hai2 : ai2 ∈ @A α I y2.succ.succ := by
                have haux : ai2 ∈ (@B α _ I y2.succ.succ) := @Finset.max'_mem α (@lo α _ hChain) (@B α _ I y2.succ.succ) (@hB α _ I hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2))
                unfold B at haux
                rw [@Finset.mem_filter α (fun a => a < I y2.succ.succ) (@decidable1 α _ I y2.succ.succ) (@A α I y2.succ.succ) ai2] at haux
                exact haux.left
              unfold A at hai2
              rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) ai2] at hai2
              obtain ⟨a, ha⟩ := hai2
              exists a
              exact ha.right
            rw [temp]
            exact h1
          have htemp : Function.invFun I ai2 < y2.succ.succ := by
            have hai2 : ai2 ∈ @A α I y2.succ.succ := by
              have haux : ai2 ∈ (@B α _ I y2.succ.succ) := @Finset.max'_mem α (@lo α _ hChain) (@B α _ I y2.succ.succ) (@hB α _ I hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2))
              unfold B at haux
              rw [@Finset.mem_filter α (fun a => a < I y2.succ.succ) (@decidable1 α _ I y2.succ.succ) (@A α I y2.succ.succ) ai2] at haux
              exact haux.left
            unfold A at hai2
            rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) ai2] at hai2
            obtain ⟨a, ha1, ha2⟩ := hai2
            have hinv : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
            have hinv : (Function.invFun I ∘ I) a = a := by
              rw [hinv]
              exact id_eq a
            have ha2 : Function.invFun I (I a) = Function.invFun I ai2 := by rw [ha2]
            have ha2 : a = Function.invFun I ai2 := by
              rw [←hinv]
              exact ha2
            rw [←ha2]
            rw [Finset.mem_range] at ha1
            exact ha1
          have h1 : @embedHelper _ _ hChain _ hI1 hI2 (y1.succ.succ) ≤
                    @embed _ _ hChain _ hI1 hI2 ai2 := ih (Function.invFun I ai2) htemp h1

          have h2 : I y1.succ.succ ≤ aj2 := by
            have htemp : I y2.succ.succ ≤ aj2 := by
              have haj2 : aj2 ∈ @C α _ I y2.succ.succ := by sorry
              unfold C at haj2
              rw [@Finset.mem_filter α (fun a => I y2.succ.succ < a) (@decidable2 α _ I y2.succ.succ) (@A α I y2.succ.succ) aj2] at haj2
              rw [le_iff_eq_or_lt]
              exact Or.inr haj2.right
            exact le_trans hnm htemp
          have h2 : I y1.succ.succ ≤ I (Function.invFun I aj2) := by
            have temp : I (Function.invFun I aj2) = aj2 := by
              apply Function.invFun_eq
              have haj2 : aj2 ∈ @A α I y2.succ.succ := by
                have haux : aj2 ∈ (@C α _ I y2.succ.succ) := @Finset.min'_mem α (@lo α _ hChain) (@C α _ I y2.succ.succ) (@hC α _ I hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2))
                unfold C at haux
                rw [@Finset.mem_filter α (fun a => I y2.succ.succ < a) (@decidable2 α _ I y2.succ.succ) (@A α I y2.succ.succ) aj2] at haux
                exact haux.left
              unfold A at haj2
              rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) aj2] at haj2
              obtain ⟨a, ha⟩ := haj2
              exists a
              exact ha.right
            rw [temp]
            exact h2
          have htemp : Function.invFun I aj2 < y2.succ.succ := by
            have haj2 : aj2 ∈ @A α I y2.succ.succ := by
              have haux : aj2 ∈ (@C α _ I y2.succ.succ) := @Finset.min'_mem α (@lo α _ hChain) (@C α _ I y2.succ.succ) (@hC α _ I hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2))
              unfold C at haux
              rw [@Finset.mem_filter α (fun a => I y2.succ.succ < a) (@decidable2 α _ I y2.succ.succ) (@A α I y2.succ.succ) aj2] at haux
              exact haux.left
            unfold A at haj2
            rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) aj2] at haj2
            obtain ⟨a, ha1, ha2⟩ := haj2
            have hinv : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
            have hinv : (Function.invFun I ∘ I) a = a := by
              rw [hinv]
              exact id_eq a
            have ha2 : Function.invFun I (I a) = Function.invFun I aj2 := by rw [ha2]
            have ha2 : a = Function.invFun I aj2 := by
              rw [←hinv]
              exact ha2
            rw [←ha2]
            rw [Finset.mem_range] at ha1
            exact ha1
          have h2 : @embedHelper _ _ hChain _ hI1 hI2 (y1.succ.succ) ≤
                    @embed _ _ hChain _ hI1 hI2 aj2 := ih (Function.invFun I aj2) htemp h2

          have h3 : embedHelper y1.succ.succ ≤ mean (embed ai2) (embed aj2) := mean_le (@embedHelper α _ hChain I hI1 hI2 y1.succ.succ)
                        (@embed _ _ hChain _ hI1 hI2 ai2)
                        (@embed _ _ hChain _ hI1 hI2 aj2)
                        h1 h2

          rw [temp2]
          simp only [embed] at h3
          rw [←le_iff_eq_or_lt]
          exact h3
        · sorry

lemma embedOrder {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α), a ≤ b → @embed _ _ hChain _ hI1 hI2 a ≤ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b hab
  unfold embed
  have ha : I (Function.invFun I a) = a := by
    apply Function.invFun_eq
    exact hI1.right a
  have hb : I (Function.invFun I b) = b := by
    apply Function.invFun_eq
    exact hI1.right b
  have hab : I (Function.invFun I a) ≤ I (Function.invFun I b) := by
    rw [ha, hb]
    exact hab
  exact @embedOrderHelper α _ hChain I hI1 hI2 (Function.invFun I a) (Function.invFun I b) hab

lemma my_min_eq_bot {hChain : chain α} {a b : α} : a ⊓ b = Bot.bot → a = Bot.bot ∨ b = Bot.bot := by
  intro h
  let hChain := hChain a b
  cases hChain
  · rename_i h1
    have temp : a ⊓ b = a := by simp [h1]
    rw [h] at temp
    simp [temp]
  · rename_i h1
    have temp : a ⊓ b = b := by simp [h1]
    rw [h] at temp
    simp [temp]

lemma embedInf {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α ), @embed _ _ hChain _ hI1 hI2 (a ⊓ b) =
    @embed _ _ hChain _ hI1 hI2 a ⊓ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b
  by_cases h : a ≤ b
  · have h1 : @embed _ _ hChain _ hI1 hI2 a ≤ embed b := @embedOrder _ _ _ _ hI1 hI2 a b h
    simp [h]
    exact h1
  · have h1 : b ≤ a := by
      have temp : a ≤ b ∨ b ≤ a := hChain a b
      by_contra
      have h2 : ¬a≤b ∧ ¬b≤a := And.intro h this
      rw [or_iff_not_and_not] at temp
      exact temp h2
    have h2 : @embed _ _ hChain _ hI1 hI2 b ≤ embed a := @embedOrder _ _ _ _ hI1 hI2 b a h1
    simp [h1]
    exact h2

lemma embedSup {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α ), @embed _ _ hChain _ hI1 hI2 (a ⊔ b) =
    @embed _ _ hChain _ hI1 hI2 a ⊔ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b
  by_cases h : a ≤ b
  · have h1 : @embed _ _ hChain _ hI1 hI2 a ≤ embed b := @embedOrder _ _ _ _ hI1 hI2 a b h
    simp [h]
    exact h1
  · have h1 : b ≤ a := by
      have temp : a ≤ b ∨ b ≤ a := hChain a b
      by_contra
      have h2 : ¬a≤b ∧ ¬b≤a := And.intro h this
      rw [or_iff_not_and_not] at temp
      exact temp h2
    have h2 : @embed _ _ hChain _ hI1 hI2 b ≤ embed a := @embedOrder _ _ _ _ hI1 hI2 b a h1
    simp [h1]
    exact h2

lemma embedTo {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α ), @embed _ _ hChain _ hI1 hI2 (a ⇨ b) =
    @embed _ _ hChain _ hI1 hI2 a ⇨ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b
  by_cases h : a ≤ b
  · have h1 : @embed _ _ hChain _ hI1 hI2 a ≤ embed b := @embedOrder _ _ _ _ hI1 hI2 a b h
    simp [himp, himpQ]
    split_ifs
    · sorry -- need to use what himp looks like in a chain, because α is a chain
  · have h1 : b ≤ a := by
      have temp : a ≤ b ∨ b ≤ a := hChain a b
      by_contra
      have h2 : ¬a≤b ∧ ¬b≤a := And.intro h this
      rw [or_iff_not_and_not] at temp
      exact temp h2
    have h2 : @embed _ _ hChain _ hI1 hI2 b ≤ embed a := @embedOrder _ _ _ _ hI1 hI2 b a h1
    sorry -- need to use what himp looks like in a chain, because α is a chain

lemma embedInj {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : Function.Injective (@embed _ _ hChain _ hI1 hI2) := by
  unfold Function.Injective
  intro a b hab
  sorry -- inductively?

lemma embedHomo {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : Qhomomorphism (@embed _ _ hChain _ hI1 hI2) := by
  apply And.intro
  · exact embedTop
  · apply And.intro
    · exact embedBot
    · intro _ _
      apply And.intro
      · exact @embedOrder _ _ _ _ _ _ _ _
      · apply And.intro
        · exact @embedInf _ _ _ _ _ _ _ _
        · apply And.intro
          · exact @embedSup _ _ _ _ _ _ _ _
          · exact @embedTo _ _ _ _ _ _ _ _

-- The embedding into Q that we want exists
lemma embedding : Countable α → chain α → ∃ (f : α → Q), Qhomomorphism f ∧ Function.Injective f := by
  intro h1 h2
  have enum : ∃ (g : ℕ → α), Function.Surjective g := exists_surjective_nat α
  obtain ⟨enum, henum⟩ := enum
  -- ensure enum is a bijection and enum bot is 0 and enum top is 1 (swap values?)
  have hg1 : Function.Bijective enum := by sorry
  have hg2 : enum 0 = Bot.bot ∧ enum 1 = Top.top := by sorry
  have hChain : LinearOrder α := @lo α _ h2
  let f := @embed _ _ h2 enum hg1 hg2
  -- use embedHomo and embedInj to conclude
  have Qhomof : Qhomomorphism f := embedHomo
  have Injf : Function.Injective f := embedInj
  exists f

-- f_quot_var will be the valuation that allows us to derive a contradiction in the completeness proof
def f_q_var {hF : filter F} {f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ _) → Q} (v : Var) :=
  f (@filter_quot_var _ _ hF v)

def f_q {hF : filter F} {f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ _) → Q} (ϕ : Formula) :=
  f (@filter_quot _ _ hF ϕ)

lemma f_q_alg_interpretation {hF : filter F} {f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ _) → Q} {hf : Qhomomorphism f}:
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

lemma countable {Γ : Set Formula} {F : Set (Quotient (@setoid_formula Γ))} {hF : filter F} :
  Countable (Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ hF)) := sorry -- use fact that there are countably many formulas

-- Gives us a valuation that sets Γ to true, but ϕ to false
lemma rational_contradicting_valuation (ϕ : Formula) : ¬Nonempty (Γ ⊢ ϕ) →
  ∃ (F : Set (Quotient (@setoid_formula Γ))) (hF : prime_filter F)
    (f : Quotient (@setoid_filter (Quotient (@setoid_formula Γ)) _ _ hF.left.left) → Q),
    Qhomomorphism f ∧
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
    Qhomomorphism f ∧ Function.Injective f := embedding countable (quotient_chain hF)
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
  · contrapose
    intro notTrueInLTAlgebra
    -- use the rational_contradicting_valuation lemma
    have h : ∃ (F : Set (Quotient (@setoid_formula Γ))) (hF : prime_filter F)
    (f : Quotient (@setoid_filter (Quotient setoid_formula) _ _ hF.left.left) → Q),
     Qhomomorphism f ∧
     set_true_in_alg_model (@f_q_var _ _ _ f) Γ ∧
    ¬true_in_alg_model (@f_q_var _ _ _ f) ϕ := by
      exact @rational_contradicting_valuation Γ ϕ notTrueInLTAlgebra
    obtain ⟨_, _, f, _, _, nhϕ⟩ := h
    -- suppose that Γ ⊨ ϕ for contradiction
    by_contra unitSemCon
    -- then in particular, Γ is true under f_q_var implies ϕ is true under f_q_var
    specialize unitSemCon (@f_q_var _ _ _ f)
    -- but then ϕ is true under f_q_var because rational_contradicting_valuation lemma
    -- assures us that Γ is true under f_q_var
    have hϕ : true_in_alg_model (@f_q_var _ _ _ f) ϕ := by
      apply unitSemCon
      assumption
    exact nhϕ hϕ
  · exact soundness_rational_unit_interval ϕ

/-
theorem completeness_rational_unit_interval1 {Γ : Set Formula} (ϕ : Formula) :
  rational_unit_interval_sem_conseq Γ ϕ ↔ Nonempty (Γ ⊢ ϕ) := by
  apply Iff.intro
  · rw [←true_in_lt]
    contrapose
    intro notTrueInLTAlgebra
    -- assume for contradiction that Γ ⊨ ϕ under chains
    by_contra unitSemCon
    let ϕModΓ := @h_quot Γ ϕ
    -- hnottop means that we can find a filter F that separates top and ϕ
    have hNotTop : ϕModΓ ≠ Top.top := by
      rw [true_in_alg_model, ← h_quot_interpretation ϕ, h_quot, le_antisymm_iff, not_and] at notTrueInLTAlgebra
      by_contra
      have h : le_quot Top.top ϕModΓ := by
        simp only [setoid_formula.eq_1, ←this]
        exact @le_refl _ _ ϕModΓ
      exact notTrueInLTAlgebra le_top h
    -- use super_prime_filter_cor1 (in Filters.lean) to get a prime filter F that separates top and ϕ
    have hF1 : ∃F, prime_filter F ∧ ϕModΓ ∉ F := by exact super_prime_filter_cor1 _ hNotTop
    obtain ⟨F, hF1⟩ := hF1
    -- use quotient_chain lemma to assert that LT/F is in fact a chain
    have hChain : @chain (Quotient (setoid_filter (f := hF1.left.left.left))) _ := by
      exact quotient_chain hF1.left
    -- introduce our valuation into LT/F that will let us derive a contradiction
    let I' (v : Var) := filter_quot_var (f := hF1.left.left.left) v
    -- show that Γ is true under I
    have hΓ : set_true_in_alg_model I' Γ := by
      intros ψ hψ
      have hψ : Quotient.mk (@setoid_formula Γ) ψ = Top.top := by
        rw [← equiv_top]
        apply Nonempty.intro
        exact Proof.premise hψ
      rw [true_in_alg_model, ←filter_quot_interpretation, filter_quot, h_quot]
      apply Quotient.sound
      simp only [HasEquiv.Equiv, setoid_filter]
      rw [hψ, equiv_filter, and_self, le, himp_self]
      exact @top_mem_filter _ _ _ hF1.left.left.left
    -- now we use the assumption that ϕ is not true in the LT algebra under h_quot_var
    have nhϕ : ¬true_in_alg_model I' ϕ := by
      -- it is sufficient to show that ϕModΓModF ≠ ⊤
      rw [true_in_alg_model, ←filter_quot_interpretation]
      -- assume for contradiction that ϕModΓModF = ⊤
      by_contra
      -- we then have ϕModΓ ~ ⊤
      have ϕEquivTop : equiv_filter (F := F) (Quotient.mk _ ϕ) Top.top := by
        exact Quotient.exact this
      -- we can now show that ϕ ∈ F, which is a contradiction
      have ϕInF : ϕModΓ ∈ F := by
        simp only [equiv_filter, le, top_himp] at ϕEquivTop
        exact ϕEquivTop.right
      exact hF1.right ϕInF

    have embed : ∃ (f : Quotient (setoid_filter (f := hF1.left.left.left)) → Q),
      homomorphism f ∧ ∀ (a b : Quotient (setoid_filter (f := hF1.left.left.left))), f a = f b → a = b := by exact embedding hChain
    obtain ⟨f, hf⟩ := embed
    -- introduce our valuation into Q that will let us derive a contradiction
    let I (v : Var) := @f_quot_var Γ F _ f v
    specialize unitSemCon I
    have hΓ : set_true_in_alg_model I Γ := by
      rw [set_true_in_alg_model]
      intros ψ hψ
      rw [true_in_alg_model,←f_alg_interpretation,f_quot,filter_quot,h_quot]
      rw [set_true_in_alg_model] at hΓ
      specialize hΓ ψ hψ
      rw [true_in_alg_model, ←filter_quot_interpretation, filter_quot, h_quot] at hΓ
      have h : f Top.top = Top.top := by exact hf.left.left
      simp only [hΓ, h]
      exact hf.left
    have hϕ : true_in_alg_model I ϕ := by
      apply unitSemCon
      exact hΓ
    have nhϕ : ¬true_in_alg_model I' ϕ := by
      -- it is sufficient to show that ϕModΓModF ≠ ⊤
      rw [true_in_alg_model, ←filter_quot_interpretation]
      -- assume for contradiction that ϕModΓModF = ⊤
      by_contra
      -- we then have ϕModΓ ~ ⊤
      have ϕEquivTop : equiv_filter (F := F) (Quotient.mk _ ϕ) Top.top := by
        exact Quotient.exact this
      -- we can now show that ϕ ∈ F, which is a contradiction
      have ϕInF : ϕModΓ ∈ F := by
        simp only [equiv_filter, le, top_himp] at ϕEquivTop
        exact ϕEquivTop.right
      exact hF1.right ϕInF
    have nhϕ : ¬true_in_alg_model I ϕ := by
      by_contra
      rw [ true_in_alg_model, ←f_alg_interpretation, f_quot] at this
      rw [ true_in_alg_model, ←filter_quot_interpretation] at nhϕ
      have h : @filter_quot Γ F hF1.left.left.left ϕ = Top.top := by
        rw [←hf.left.left] at this
        exact hf.right (@filter_quot Γ F hF1.left.left.left ϕ) Top.top this
      exact nhϕ h
      exact hf.left
    exact nhϕ hϕ
  · exact soundness_rational_unit_interval ϕ
-/
/-
lemma embedInf1 [LinearOrder α] {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α ), @embed _ _ _ _ hI1 hI2 (a ⊓ b) =
    @embed _ _ _ _ hI1 hI2 a ⊓ @embed _ _ _ _ hI1 hI2 b := by
  have nt : Nontrivial α := @Function.Injective.nontrivial ℕ α _ I hI1.left
  intro a b
  unfold embed
  unfold embedHelper
  --simp
  split
  · split
    · simp
      exact bot_le
    · split
      · simp
      · rename_i h1 _ h2 _ h3
        simp
        have h1 : a ⊓ b = Bot.bot := by
          rw [←@IinvEqZeroIff _ _ (a ⊓ b) I hI1 hI2]
          exact h1
        have h2 : a = Top.top := by
          rw [←@IinvEqOneIff _ _ a I hI1 hI2]
          exact h2
        have h3 : b = Top.top := by
          rw [←@IinvEqOneIff _ _ b I hI1 hI2]
          exact h3
        have h4 : a ⊓ b = Top.top := by
          rw [h2, h3]
          simp
        have h5 : ¬a ⊓ b = Top.top := by
          rw [h1]
          simp
        exact h5 h4
      · exfalso
        have h1 : a ⊓ b = Bot.bot := by
          rw [←@IinvEqZeroIff _ _ (a ⊓ b) I hI1 hI2]
          assumption
        have h2 : a = Top.top := by
          rw [←@IinvEqOneIff _ _ a I hI1 hI2]
          assumption
        have temp : a = Bot.bot ∨ b = Bot.bot := my_min_eq_bot h1
        by_cases h3 : b = Bot.bot
        · have h4 : Function.invFun I b = 0 := by
            rw [@IinvEqZeroIff _ _ b I hI1 hI2 ]
            exact h3
          rename_i h5 _
          apply h5
          exact h4
        · have temp : a = Bot.bot := by
            by_contra
            have h6 : ¬a=Bot.bot ∧ ¬b=Bot.bot := And.intro this h3
            have h7 : ¬(¬a=Bot.bot ∧ ¬b=Bot.bot) := by
              rw [←or_iff_not_and_not]
              exact temp
            exact h7 h6
          rw [h2] at temp
          exact top_ne_bot temp
    · split
      · simp
        exact bot_le
      · exfalso
        rename_i h1 _ h2 _ _ h3
        have h4 : a ⊓ b = Bot.bot := by
          rw [←@IinvEqZeroIff _ _ (a ⊓ b) I hI1 hI2]
          exact h1
        have h5 : b = Top.top := by
          rw [←@IinvEqOneIff _ _ b I hI1 hI2]
          exact h3
        have h6 : a = Bot.bot ∨ b = Bot.bot := my_min_eq_bot h4
        have h7 : ¬b = Bot.bot := by
          rw [h5]
          simp only [top_ne_bot, not_false_eq_true]
        have h8 : a = Bot.bot := by
          by_contra
          have h9 : ¬a=Bot.bot ∧ ¬b=Bot.bot := And.intro this h7
          rw [or_iff_not_and_not] at h6
          exact h6 h9
        rw [@IinvEqZeroIff _ _ a I hI1 hI2] at h2
        exact h2 h8
      · exfalso
        rename_i h1 _ h2 _ _ h3 _
        have h4 : a ⊓ b = Bot.bot := by
          rw [←@IinvEqZeroIff _ _ (a ⊓ b) I hI1 hI2]
          exact h1
        have h5 : a = Bot.bot ∨ b = Bot.bot := my_min_eq_bot h4
        cases h5
        · rename_i h6
          rw [←@IinvEqZeroIff _ _ a I hI1 hI2] at h6
          exact h2 h6
        · rename_i h6
          rw [←@IinvEqZeroIff _ _ b I hI1 hI2] at h6
          exact h3 h6
  · split
    · exfalso
      rename_i h1 _ h2
      have h3 : a ⊓ b = Top.top := by
        rw [←@IinvEqOneIff _ _ (a ⊓ b) I hI1 hI2]
        exact h1
      have h4 : a = Bot.bot := by
        rw [←@IinvEqZeroIff _ _ a I hI1 hI2]
        exact h2
      simp at h3
      rw [h3.left] at h4
      have h5 : ¬(Top.top : α) = Bot.bot := top_ne_bot
      exact h5 h4
    · split
      · exfalso
        rename_i h1 _ _ _ h2
        have h1 : a ⊓ b = Top.top := by
          rw [←@IinvEqOneIff _ _ _ _ hI1 hI2]
          exact h1
        have h2 : b = Bot.bot := by
          rw [←@IinvEqZeroIff _ _ _ _ hI1 hI2]
          exact h2
        rw [inf_eq_top_iff] at h1
        have h3 : ¬b=Top.top := by
          rw [h2]
          simp
        exact h3 h1.right
      · simp
      · exfalso
        rename_i h1 _ _ _ _ h2
        have h1 : a ⊓ b = Top.top := by
          rw [←@IinvEqOneIff _ _ _ _ hI1 hI2]
          exact h1
        rw [inf_eq_top_iff] at h1
        rw [@IinvEqOneIff _ _ _ _ hI1 hI2] at h2
        exact h2 h1.right
    · exfalso
      rename_i h1 _ _ h2
      have h1 : a ⊓ b = Top.top := by
        rw [←@IinvEqOneIff _ _ _ _ hI1 hI2]
        exact h1
      rw [inf_eq_top_iff] at h1
      rw [@IinvEqOneIff _ _ _ _ hI1 hI2] at h2
      exact h2 h1.left
  · split
    · exfalso
      sorry
    · split
      · exfalso
        sorry
      · exfalso
        sorry
      · have temp : a ⊓ b = b := by sorry
        rw [temp]
        simp
        exact le_top
    · split
      · exfalso
        sorry
      · have temp : a ⊓ b = a := by sorry
        rw [temp]
        simp
        exact le_top
      · sorry
-/
-- definition of embedHelper using Nat.strongRec
/-noncomputable def embedHelper [LinearOrder α] {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : ℕ → Q :=
  Nat.strongRec
    (fun n prev =>
      match n with
      | 0 => ⟨0, zero_memQ⟩
      | 1 => ⟨1, one_memQ⟩
      | x =>
          let A : Finset α := Finset.image I (Finset.range x)
          have h1 : DecidablePred (fun a => a < I x) := by sorry
          have h2 : DecidablePred (fun a => I x < a) := by sorry
          let B := A.filter (fun a => a < I x)
          let C := A.filter (fun a => I x < a)
          have hB : B.Nonempty := by sorry
          have hC : C.Nonempty := by sorry
          let ai := B.max' hB
          let aj := C.min' hC
          let I_inv := Function.invFun I
          let ai' := prev (I_inv ai) (by sorry)
          let aj' := prev (I_inv aj) (by sorry)
          mean ai' aj'
    )-/
/-lemma IinvEqZeroIff {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  Function.invFun I a = 0 ↔ a = Bot.bot := by
  apply Iff.intro
  intro h
  rw [←hI2.left]
  have h1 : I (Function.invFun I a) = I 0 := by simp [h]
  have h2 : ∃(b : ℕ), I b = a := by
    exact hI1.right a
  have h3 : I (Function.invFun I a) = a := by exact Function.invFun_eq h2
  rw [h1] at h3
  simp [h3]
  intro h
  have h1 : I 0 = Bot.bot := by exact hI2.left
  rw [← h1] at h
  have h2 : Function.invFun I a = Function.invFun I (I 0) := by simp [h]
  have h3 : Function.invFun I ∘ I = id := by exact @Function.invFun_comp _ _ _ _ hI1.left
  have h4 : (Function.invFun I ∘ I) 0 = 0 := by
    rw [h3]
    exact id_eq 0
  rw [h2]
  exact h4

lemma IinvEqOneIff {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  Function.invFun I a = 1 ↔ a = Top.top := by
  apply Iff.intro
  intro h
  rw [←hI2.right]
  have h1 : I (Function.invFun I a) = I 1 := by simp [h]
  have h2 : ∃(b : ℕ), I b = a := by
    exact hI1.right a
  have h3 : I (Function.invFun I a) = a := Function.invFun_eq h2
  rw [h1] at h3
  simp [h3]
  intro h
  have h1 : I 1 = Top.top := hI2.right
  rw [← h1] at h
  have h2 : Function.invFun I a = Function.invFun I (I 1) := by simp [h]
  have h3 : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
  have h4 : (Function.invFun I ∘ I) 1 = 1 := by
    rw [h3]
    exact id_eq 1
  rw [h2]
  exact h4-/
