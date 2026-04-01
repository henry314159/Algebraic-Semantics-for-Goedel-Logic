import GoedelLogic.RationalUnitIntervalSoundness
import GoedelLogic.ChainCompleteness
import GoedelLogic.Formula
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Denumerable

-- Older than RationalUnitIntervalCompleteness.lean

set_option pp.proofs true

variable {α : Type} [LAlgebra α]
variable {Γ : Set Formula}
variable {F : Set (Quotient (@setoid_formula Γ))}

-- Show that a chain is a linear order
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

-- Define what it means for a function f : α → Q to be a homomorphism
def Q_homomorphism (f : α → Q) : Prop := f Top.top = Top.top ∧
                f Bot.bot = Bot.bot ∧
                ∀ (a b : α),  (a ≤ b → f a ≤ f b) ∧
                f (a ⊓ b) = f a ⊓ f b ∧
                f (a ⊔ b) = f a ⊔ f b ∧
                f (a ⇨ b) = f a ⇨ f b

-- We need to enumerate the values in α such that ⊥ and ⊤ come first
def I01 (I : ℕ → α) : Prop := I 0 = Bot.bot ∧ I 1 = Top.top

noncomputable def A {I : ℕ → α} (n : ℕ) : Finset α :=
  Finset.image I (Finset.range n)

noncomputable instance decidable_lt {I : ℕ → α} (n : ℕ) :
  DecidablePred (fun a => a < I n) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h1 : a < I n
  · exact isTrue h1
  · exact isFalse h1

noncomputable instance decidable_gt {I : ℕ → α} (n : ℕ) :
  DecidablePred (fun a => I n < a) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h1 : I n < a
  · exact isTrue h1
  · exact isFalse h1

noncomputable def B {I : ℕ → α} (n : ℕ) : Finset α :=
  @(@A α I n).filter α (fun a => a < I n) (decidable_lt n)

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
    have temp : n ≠ 0 := by
      by_contra
      rw [this] at hn
      rw [← @lt_self_iff_false ℕ]
      exact lt_trans Nat.one_lt_ofNat (Nat.lt_add_one_of_le hn)
    have h3 : I n ≠ Bot.bot := inj temp
    by_contra
    rw [not_bot_lt_iff] at this
    exact h3 this

noncomputable def C {I : ℕ → α} (n : ℕ) : Finset α :=
  @(@A α I n).filter α (fun a => I n < a) (decidable_gt n)

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
    have temp : n ≠ 1 := by
      by_contra
      rw [this] at hn
      rw [← @lt_self_iff_false ℕ]
      exact Nat.lt_add_one_of_le hn
    have h3 : I n ≠ Top.top := inj temp
    by_contra
    rw [not_lt_top_iff] at this
    exact h3 this

noncomputable def ai {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) (hn : 2 ≤ n) : α :=
  @Finset.max' α (@linear_order_chain α _ hChain) (@B α _ I n) (@hB α _ I hI1 hI2 n hn)

noncomputable def aj {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) (hn : 2 ≤ n) : α :=
  @Finset.min' α (@linear_order_chain α _ hChain) (@C α _ I n) (@hC α _ I hI1 hI2 n hn)

lemma decreasing_ai {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} {y : ℕ} :
  Function.invFun I (@ai _ _ hChain _ hI1 hI2 y.succ.succ (Nat.le_add_left 2 y)) < y.succ.succ := by
  let ai' := @ai α _ hChain _ hI1 hI2 y.succ.succ (Nat.le_add_left 2 y)
  have hai : ai' ∈ @A α I y.succ.succ := by
    have haux : ai' ∈ (@B α _ I y.succ.succ) := @Finset.max'_mem α (@linear_order_chain α _ hChain) (@B α _ I y.succ.succ) (@hB α _ I hI1 hI2 y.succ.succ (Nat.le_add_left 2 y))
    unfold B at haux
    rw [@Finset.mem_filter α (fun a => a < I y.succ.succ) (@decidable_lt α _ I y.succ.succ) (@A α I y.succ.succ) ai'] at haux
    exact haux.left
  unfold A at hai
  rw [@Finset.mem_image ℕ α _ I (Finset.range y.succ.succ) ai'] at hai
  obtain ⟨a, ha1, ha2⟩ := hai
  have hinv : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
  have hinv : (Function.invFun I ∘ I) a = a := by
    rw [hinv]
    exact id_eq a
  have ha2 : Function.invFun I (I a) = Function.invFun I ai' := by rw [ha2]
  have ha2 : a = Function.invFun I ai' := by
    rw [←hinv]
    exact ha2
  rw [←ha2]
  rw [Finset.mem_range] at ha1
  exact ha1

lemma decreasing_aj {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} {y : ℕ} :
  Function.invFun I (@aj _ _ hChain _ hI1 hI2 y.succ.succ (Nat.le_add_left 2 y)) < y.succ.succ := by
  let aj' := @aj α _ hChain _ hI1 hI2 y.succ.succ (Nat.le_add_left 2 y)
  have haj : aj' ∈ @A α I y.succ.succ := by
    have haux : aj' ∈ (@C α _ I y.succ.succ) := @Finset.min'_mem α (@linear_order_chain α _ hChain) (@C α _ I y.succ.succ) (@hC α _ I hI1 hI2 y.succ.succ (Nat.le_add_left 2 y))
    unfold C at haux
    rw [@Finset.mem_filter α (fun a => I y.succ.succ < a) (@decidable_gt α _ I y.succ.succ) (@A α I y.succ.succ) aj'] at haux
    exact haux.left
  unfold A at haj
  rw [@Finset.mem_image ℕ α _ I (Finset.range y.succ.succ) aj'] at haj
  obtain ⟨a, ha1, ha2⟩ := haj
  have hinv : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
  have hinv : (Function.invFun I ∘ I) a = a := by
    rw [hinv]
    exact id_eq a
  have ha2 : Function.invFun I (I a) = Function.invFun I aj' := by rw [ha2]
  have ha2 : a = Function.invFun I aj' := by
    rw [←hinv]
    exact ha2
  rw [←ha2]
  rw [Finset.mem_range] at ha1
  exact ha1

-- Defines the embedding assuming we have a suitable enumeration of the elements in the chain
noncomputable def embed_helper {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (n : ℕ) : Q :=
  match n with
  | 0 => ⟨0, zero_mem_Q⟩
  | 1 => ⟨1, one_mem_Q⟩
  | Nat.succ (Nat.succ y) =>
      mean (@embed_helper hChain I hI1 hI2 (Function.invFun I (@ai α _ hChain _ hI1 hI2 (Nat.succ (Nat.succ y)) (Nat.le_add_left 2 y))))
           (@embed_helper hChain I hI1 hI2 (Function.invFun I (@aj α _ hChain _ hI1 hI2 (Nat.succ (Nat.succ y)) (Nat.le_add_left 2 y))))
  decreasing_by
    · exact decreasing_ai
    · exact decreasing_aj

-- Embed is our monomorphism (a.k.a. embedding, or injective homomorphism) A/F → [0,1]_ℚ
noncomputable def embed {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} (a : α) : Q :=
  @embed_helper _ _ hChain _ hI1 hI2 (Function.invFun I a)

lemma embed_top {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : @embed α _ hChain I hI1 hI2 Top.top = Top.top := by
  have h_inv : Function.invFun I Top.top = 1 := by
    rw [←hI2.right]
    have h1 : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
    have h2 : (Function.invFun I ∘ I) 1 = 1 := by
      rw [h1]
      exact id_eq 1
    exact h2
  rw [embed, h_inv, embed_helper]
  rfl

lemma embed_bot {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : @embed α _ hChain I hI1 hI2 Bot.bot = Bot.bot := by
  have h_inv : Function.invFun I Bot.bot = 0 := by
    rw [←hI2.left]
    have h1 : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ _ hI1.left
    have h2 : (Function.invFun I ∘ I) 0 = 0 := by
      rw [h1]
      exact id_eq 0
    exact h2
  rw [embed, h_inv, embed_helper]
  rfl

lemma embed_helper_order_helper {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (k : ℕ), ∀ (m n : ℕ), m ≤ k → n ≤ k → I m < I n →
    @embed_helper _ _ hChain _ hI1 hI2 m < @embed_helper _ _ hChain _ hI1 hI2 n := by
  intro k
  induction k with
  | zero =>
      intro m n hm hn hI
      exfalso
      have hm : m = 0 := by
        rw [←Nat.le_zero]
        exact hm
      have hn : n = 0 := by
        rw [←Nat.le_zero]
        exact hn
      rw [hm, hn] at hI
      rw [← @lt_self_iff_false α]
      exact hI
  | succ k ih =>
      intro m n
      by_cases hm : m = k + 1
      · by_cases hn : n = k + 1
        · intro _ _ hI
          rw [hm, hn] at hI
          exfalso
          rw [← @lt_self_iff_false α]
          exact hI
        · intro hm' hn' hmn
          have hn : n < k + 1 := by
            rw [lt_iff_le_and_ne]
            exact And.intro hn' hn
          have hn : n ≤ k := by
            rw [Nat.le_iff_lt_add_one]
            exact hn
          unfold embed_helper
          split
          · exfalso
            have hn : n = 0 := by
              rw [← hm] at hn'
              rw [← Nat.le_zero]
              exact hn'
            rw [hn] at hmn
            rw [← @lt_self_iff_false α]
            exact hmn
          · exfalso
            have hk : k = 0 := by
              rw [← right_eq_add]
              exact hm
            have hn : n = 0 := by
              rw [hk] at hn
              rw [← Nat.le_zero]
              exact hn
            rw [hn] at hmn
            rw [hI2.left, hI2.right] at hmn
            exact not_lt_bot hmn
          · split
            · exfalso
              rw [hI2.left] at hmn
              exact not_lt_bot hmn
            · rw [lt_iff_le_and_ne]
              apply And.intro
              · exact le_top
              · by_contra
                rename_i y _ _ _
                rw [mean_eq_one] at this
                let ai' := @ai α _ hChain _ hI1 hI2 y.succ.succ (embed_helper._proof_4 y)
                have hai1 : ai' < I y.succ.succ := by
                  have haux : ai' ∈ (@B α _ I y.succ.succ) := @Finset.max'_mem α (@linear_order_chain α _ hChain) (@B α _ I y.succ.succ) (@hB α _ I hI1 hI2 y.succ.succ (Nat.le_add_left 2 y))
                  unfold B at haux
                  rw [@Finset.mem_filter α (fun a => a < I y.succ.succ) (@decidable_lt α _ I y.succ.succ) (@A α I y.succ.succ) ai'] at haux
                  exact haux.right
                have hai1 : ai' < I 1 := lt_trans hai1 hmn
                have hai1 : I (Function.invFun I ai') < I 1 := by
                  have temp : I (Function.invFun I ai') = ai' := by
                    apply Function.invFun_eq
                    have hai' : ai' ∈ @A α I y.succ.succ := by
                      have haux : ai' ∈ (@B α _ I y.succ.succ) := @Finset.max'_mem α (@linear_order_chain α _ hChain) (@B α _ I y.succ.succ) (@hB α _ I hI1 hI2 y.succ.succ (Nat.le_add_left 2 y))
                      unfold B at haux
                      rw [@Finset.mem_filter α (fun a => a < I y.succ.succ) (@decidable_lt α _ I y.succ.succ) (@A α I y.succ.succ) ai'] at haux
                      exact haux.left
                    unfold A at hai'
                    rw [@Finset.mem_image ℕ α _ I (Finset.range y.succ.succ) ai'] at hai'
                    obtain ⟨a, ha⟩ := hai'
                    exists a
                    exact ha.right
                  rw [temp]
                  exact hai1
                have hai2 : Function.invFun I ai' < y.succ.succ := decreasing_ai
                have hai2 : Function.invFun I ai' ≤ k := by
                  rw [hm] at hai2
                  rw [← Nat.lt_add_one_iff]
                  exact hai2
                have hai3 : @embed_helper _ _ hChain _ hI1 hI2 (Function.invFun I ai') <
                            @embed_helper _ _ hChain _ hI1 hI2 1 :=
                  ih (Function.invFun I ai') 1 hai2 hn hai1
                have temp : @embed _ _ hChain _ hI1 hI2 (⊤ : α) = @embed_helper _ _ hChain _ hI1 hI2 1 := by
                  unfold embed
                  rw [← hI2.right]
                  have temp1 : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ I hI1.left
                  have temp2 : Function.invFun I (I 1) = (Function.invFun I ∘ I) 1 := by rfl
                  have temp3 : Function.invFun I (I 1) = 1 := by
                    rw [temp2, temp1]
                    rfl
                  rw [temp3]
                rw [←temp, embed_top] at hai3
                rw [lt_iff_le_and_ne] at hai3
                exact hai3.right this.left
            · rename_i n1 y1 n2 y2 _ _
              let ai1 := @ai α _ hChain _ hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1)
              let aj1 := @aj α _ hChain _ hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1)
              let ai2 := @ai α _ hChain _ hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2)
              let aj2 := @aj α _ hChain _ hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2)
              have temp1 : @embed_helper _ _ hChain _ hI1 hI2 (y1.succ.succ) = mean (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I ai1))
                        (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I aj1)) := by rw [embed_helper]
              have temp2 : @embed_helper _ _  hChain _ hI1 hI2 (y2.succ.succ) = mean (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I ai2))
                        (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I aj2)) := by rw [embed_helper]
              simp only [ai1, aj1, ai2, aj2, ←temp1, ←temp2]
              have h1 : Function.invFun I aj1 < y1.succ.succ := decreasing_aj
              have h1 : Function.invFun I aj1 ≤ k := by
                rw [hm] at h1
                rw [Nat.le_iff_lt_add_one]
                exact h1
              have h2 : aj1 ≤ I y2.succ.succ := by
                have temp : I y2.succ.succ ∈ @C _ _ I y1.succ.succ := by
                  unfold C
                  rw [@Finset.mem_filter α (fun a => I y1.succ.succ < a) (@decidable_gt α _ I y1.succ.succ) (@A α I y1.succ.succ) (I y2.succ.succ)]
                  apply And.intro
                  · unfold A
                    rw [@Finset.mem_image ℕ α _ I (Finset.range y1.succ.succ) (I y2.succ.succ)]
                    exists y2.succ.succ
                    apply And.intro
                    · rw [Finset.mem_range]
                      rename_i temp' _
                      rw [← hm] at temp'
                      exact temp'
                    · rfl
                  · exact hmn
                exact @Finset.min'_le α (@linear_order_chain α _ hChain) (@C _ _ _ y1.succ.succ) (I y2.succ.succ) temp
              have h2 : I (Function.invFun I aj1) ≤ I y2.succ.succ := by
                have temp : I (Function.invFun I aj1) = aj1 := by
                  apply Function.invFun_eq
                  have haj1 : aj1 ∈ @A α I y1.succ.succ := by
                    have haux : aj1 ∈ (@C α _ I y1.succ.succ) := @Finset.min'_mem α (@linear_order_chain α _ hChain) (@C α _ I y1.succ.succ) (@hC α _ I hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1))
                    unfold C at haux
                    rw [@Finset.mem_filter α (fun a => I y1.succ.succ < a) (@decidable_gt α _ I y1.succ.succ) (@A α I y1.succ.succ) aj1] at haux
                    exact haux.left
                  unfold A at haj1
                  rw [@Finset.mem_image ℕ α _ I (Finset.range y1.succ.succ) aj1] at haj1
                  obtain ⟨a, ha⟩ := haj1
                  exists a
                  exact ha.right
                rw [temp]
                exact h2
              have h3 : @embed_helper _ _ hChain _ hI1 hI2 (Function.invFun I aj1) ≤ @embed_helper _ _ hChain _ hI1 hI2 y2.succ.succ := by
                by_cases htemp : I (Function.invFun I aj1) = I y2.succ.succ
                · have htemp : Function.invFun I aj1 = y2.succ.succ := hI1.left htemp
                  have htemp : @embed_helper _ _ hChain _ hI1 hI2 (Function.invFun I aj1) = @embed_helper _ _ hChain _ hI1 hI2 y2.succ.succ := by
                    rw [htemp]
                  rw [le_iff_lt_or_eq]
                  exact Or.inr htemp
                · have htemp : I (Function.invFun I aj1) < I y2.succ.succ := by
                    rw [lt_iff_le_and_ne]
                    exact And.intro h2 htemp
                  rw [le_iff_lt_or_eq]
                  exact Or.inl (ih (Function.invFun I aj1) y2.succ.succ h1 hn htemp)
              have h4 : Function.invFun I ai1 < y1.succ.succ := decreasing_ai
              have h4 : Function.invFun I ai1 ≤ k := by
                rw [hm] at h4
                rw [←Nat.lt_add_one_iff]
                exact h4
              have h5 : ai1 < I y1.succ.succ := by
                have haux : ai1 ∈ (@B α _ I y1.succ.succ) := @Finset.max'_mem α (@linear_order_chain α _ hChain) (@B α _ I y1.succ.succ) (@hB α _ I hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1))
                unfold B at haux
                rw [@Finset.mem_filter α (fun a => a < I y1.succ.succ) (@decidable_lt α _ I y1.succ.succ) (@A α I y1.succ.succ) ai1] at haux
                exact haux.right
              have h5 : I (Function.invFun I ai1) < I y1.succ.succ := by
                have hinv : I (Function.invFun I ai1) = ai1 := by
                  apply Function.invFun_eq
                  exact hI1.right ai1
                rw [hinv]
                exact h5
              have h6 : I (Function.invFun I ai1) < I y2.succ.succ := lt_trans h5 hmn
              have h7 : @embed_helper _ _ _ _ hI1 hI2 (Function.invFun I ai1) < @embed_helper _ _ _ _ hI1 hI2 y2.succ.succ :=
                ih (Function.invFun I ai1) y2.succ.succ h4 hn h6

              have h8 : mean (embed ai1) (embed aj1) < embed_helper y2.succ.succ :=
                mean_lt (@embed _ _ _ _ hI1 hI2 ai1)
                        (@embed _ _ _ _ hI1 hI2 aj1)
                        (@embed_helper _ _ _ _ hI1 hI2 y2.succ.succ)
                        h7 h3
              rw [temp1]
              simp only [embed] at h8
              exact h8
      · by_cases hn : n = k + 1
        · intro hm' hn' hmn
          have hm : m < k + 1 := by
            rw [lt_iff_le_and_ne]
            exact And.intro hm' hm
          have hn : m ≤ k := by
            rw [Nat.le_iff_lt_add_one]
            exact hm
          unfold embed_helper
          split
          · split
            · exfalso
              rw [hI2.left] at hmn
              exact not_lt_bot hmn
            · simp
            · rw [lt_iff_le_and_ne]
              apply And.intro
              · exact bot_le
              · apply Ne.symm
                by_contra
                rename_i y
                rw [mean_eq_zero] at this
                let aj' := @aj α _ hChain _ hI1 hI2 y.succ.succ (embed_helper._proof_4 y)
                have haj1 : I y.succ.succ < aj' := by
                  have haux : aj' ∈ (@C α _ I y.succ.succ) := @Finset.min'_mem α (@linear_order_chain α _ hChain) (@C α _ I y.succ.succ) (@hC α _ I hI1 hI2 y.succ.succ (Nat.le_add_left 2 y))
                  unfold C at haux
                  rw [@Finset.mem_filter α (fun a => I y.succ.succ < a) (@decidable_gt α _ I y.succ.succ) (@A α I y.succ.succ) aj'] at haux
                  exact haux.right
                have haj1 : I 0 < aj' := lt_trans hmn haj1
                have haj1 : I 0 < I (Function.invFun I aj') := by
                  have temp : I (Function.invFun I aj') = aj' := by
                    apply Function.invFun_eq
                    have haj' : aj' ∈ @A α I y.succ.succ := by
                      have haux : aj' ∈ (@C α _ I y.succ.succ) := @Finset.min'_mem α (@linear_order_chain α _ hChain) (@C α _ I y.succ.succ) (@hC α _ I hI1 hI2 y.succ.succ (Nat.le_add_left 2 y))
                      unfold C at haux
                      rw [@Finset.mem_filter α (fun a => I y.succ.succ < a) (@decidable_gt α _ I y.succ.succ) (@A α I y.succ.succ) aj'] at haux
                      exact haux.left
                    unfold A at haj'
                    rw [@Finset.mem_image ℕ α _ I (Finset.range y.succ.succ) aj'] at haj'
                    obtain ⟨a, ha⟩ := haj'
                    exists a
                    exact ha.right
                  rw [temp]
                  exact haj1
                have haj2 : Function.invFun I aj' < y.succ.succ := decreasing_aj
                have haj2 : Function.invFun I aj' ≤ k := by
                  rw [hn] at haj2
                  rw [← Nat.lt_add_one_iff]
                  exact haj2
                rename_i hk _ _ _ _
                have haj3 : @embed_helper _ _ hChain _ hI1 hI2 0 <
                            @embed_helper _ _ hChain _ hI1 hI2 (Function.invFun I aj') :=
                  ih 0 (Function.invFun I aj') hk haj2 haj1
                have temp : @embed _ _ hChain _ hI1 hI2 (⊥ : α) = @embed_helper _ _ hChain _ hI1 hI2 0 := by
                  unfold embed
                  rw [← hI2.left]
                  have temp1 : Function.invFun I ∘ I = id := @Function.invFun_comp _ _ _ I hI1.left
                  have temp2 : Function.invFun I (I 0) = (Function.invFun I ∘ I) 0 := by rfl
                  have temp3 : Function.invFun I (I 0) = 0 := by
                    rw [temp2, temp1]
                    rfl
                  rw [temp3]
                rw [←temp, embed_bot] at haj3
                rw [lt_iff_le_and_ne] at haj3
                have this : ⟨0, zero_mem_Q⟩ =
                            @embed_helper _ _ hChain _ hI1 hI2
                              (Function.invFun I (@aj _ _ hChain _ hI1 hI2 y.succ.succ (embed_helper._proof_4 y))) := by
                  apply Eq.symm
                  exact this.right
                exact haj3.right this
          · exfalso
            rw [hI2.right] at hmn
            exact not_top_lt hmn
          · split
            · exfalso
              rw [hI2.left] at hmn
              exact not_lt_bot hmn
            · exfalso
              have hk : k = 0 := by
                rw [← right_eq_add]
                exact hn
              simp [hk] at hm
            · rename_i n1 y1 _ _ n2 y2
              let ai1 := @ai α _ hChain _ hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1)
              let aj1 := @aj α _ hChain _ hI1 hI2 y1.succ.succ (Nat.le_add_left 2 y1)
              let ai2 := @ai α _ hChain _ hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2)
              let aj2 := @aj α _ hChain _ hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2)
              have temp1 : @embed_helper _ _ hChain _ hI1 hI2 (y1.succ.succ) = mean (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I ai1))
                        (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I aj1)) := by rw [embed_helper]
              have temp2 : @embed_helper _ _ hChain _ hI1 hI2 (y2.succ.succ) = mean (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I ai2))
                        (@embed_helper α _ hChain I hI1 hI2 (Function.invFun I aj2)) := by rw [embed_helper]
              simp only [ai1, aj1, ai2, aj2, ←temp1, ←temp2]
              rename_i _ hm''
              have h1 : I y1.succ.succ ≤ ai2 := by -- ai2 is largest such < I y2.succ.succ
                have temp : I y1.succ.succ ∈ @B _ _ I y2.succ.succ := by
                  unfold B
                  rw [@Finset.mem_filter α (fun a => a < I y2.succ.succ) (@decidable_lt α _ I y2.succ.succ) (@A α I y2.succ.succ) (I y1.succ.succ)]
                  apply And.intro
                  · unfold A
                    rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) (I y1.succ.succ)]
                    exists y1.succ.succ
                    apply And.intro
                    · rw [Finset.mem_range]
                      rw [← hn] at hm
                      exact hm
                    · rfl
                  · exact hmn
                exact @Finset.le_max' α (@linear_order_chain α _ hChain) (@B _ _ I y2.succ.succ) (I y1.succ.succ) temp
              have h1 : I y1.succ.succ ≤ I (Function.invFun I ai2) := by
                have temp : I (Function.invFun I ai2) = ai2 := by
                  apply Function.invFun_eq
                  have hai2 : ai2 ∈ @A α I y2.succ.succ := by
                    have haux : ai2 ∈ (@B α _ I y2.succ.succ) := @Finset.max'_mem α (@linear_order_chain α _ hChain) (@B α _ I y2.succ.succ) (@hB α _ I hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2))
                    unfold B at haux
                    rw [@Finset.mem_filter α (fun a => a < I y2.succ.succ) (@decidable_lt α _ I y2.succ.succ) (@A α I y2.succ.succ) ai2] at haux
                    exact haux.left
                  unfold A at hai2
                  rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) ai2] at hai2
                  obtain ⟨a, ha⟩ := hai2
                  exists a
                  exact ha.right
                rw [temp]
                exact h1
              have h2 : Function.invFun I ai2 < y2.succ.succ := decreasing_ai
              have h2 : Function.invFun I ai2 ≤ k := by
                rw [hn] at h2
                rw [←Nat.lt_add_one_iff]
                exact h2
              have h3 : @embed_helper _ _ hChain _ hI1 hI2 y1.succ.succ ≤ @embed_helper _ _ hChain _ hI1 hI2 (Function.invFun I ai2) := by
                by_cases htemp : I y1.succ.succ = I (Function.invFun I ai2)
                · have htemp : y1.succ.succ = Function.invFun I ai2 := hI1.left htemp
                  have htemp : @embed_helper _ _ hChain _ hI1 hI2 y1.succ.succ = @embed_helper _ _ hChain _ hI1 hI2 (Function.invFun I ai2) := by
                    rw [htemp]
                  rw [le_iff_lt_or_eq]
                  exact Or.inr htemp
                · have htemp : I y1.succ.succ < I (Function.invFun I ai2) := by
                    rw [lt_iff_le_and_ne]
                    exact And.intro h1 htemp
                  rw [le_iff_lt_or_eq]
                  exact Or.inl (ih y1.succ.succ (Function.invFun I ai2) hm'' h2 htemp)

              have h4 : I y1.succ.succ < aj2 := by
                have htemp : I y2.succ.succ < aj2 := by
                  have haj2 : aj2 ∈ @C α _ I y2.succ.succ := @Finset.min'_mem α (@linear_order_chain α _ hChain) (@C α _ I y2.succ.succ) (@hC α _ I hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2))
                  unfold C at haj2
                  rw [@Finset.mem_filter α (fun a => I y2.succ.succ < a) (@decidable_gt α _ I y2.succ.succ) (@A α I y2.succ.succ) aj2] at haj2
                  exact haj2.right
                exact lt_trans hmn htemp
              have h4 : I y1.succ.succ < I (Function.invFun I aj2) := by
                have temp : I (Function.invFun I aj2) = aj2 := by
                  apply Function.invFun_eq
                  have haj2 : aj2 ∈ @A α I y2.succ.succ := by
                    have haux : aj2 ∈ (@C α _ I y2.succ.succ) := @Finset.min'_mem α (@linear_order_chain α _ hChain) (@C α _ I y2.succ.succ) (@hC α _ I hI1 hI2 y2.succ.succ (Nat.le_add_left 2 y2))
                    unfold C at haux
                    rw [@Finset.mem_filter α (fun a => I y2.succ.succ < a) (@decidable_gt α _ I y2.succ.succ) (@A α I y2.succ.succ) aj2] at haux
                    exact haux.left
                  unfold A at haj2
                  rw [@Finset.mem_image ℕ α _ I (Finset.range y2.succ.succ) aj2] at haj2
                  obtain ⟨a, ha⟩ := haj2
                  exists a
                  exact ha.right
                rw [temp]
                exact h4
              have h5 : Function.invFun I aj2 < y2.succ.succ := decreasing_aj
              have h5 : Function.invFun I aj2 ≤ k := by
                rw [hn] at h5
                rw [←Nat.lt_add_one_iff]
                exact h5
              have h6 : @embed_helper _ _ _ _ hI1 hI2 y1.succ.succ < @embed_helper _ _ _ _ hI1 hI2 (Function.invFun I aj2) :=
                ih y1.succ.succ (Function.invFun I aj2) hm'' h5 h4

              have h8 : embed_helper y1.succ.succ < mean (embed ai2) (embed aj2) :=
                lt_mean (@embed_helper _ _ _ _ hI1 hI2 y1.succ.succ)
                        (@embed _ _ _ _ hI1 hI2 ai2)
                        (@embed _ _ _ _ hI1 hI2 aj2)
                        h3 h6

              rw [temp2]
              simp only [embed] at h8
              exact h8
        · intro hm' hn' hmn
          have hm : m < k + 1 := by
            rw [lt_iff_le_and_ne]
            exact And.intro hm' hm
          have hm : m ≤ k := by
            rw [Nat.le_iff_lt_add_one]
            exact hm
          have hn : n < k + 1 := by
            rw [lt_iff_le_and_ne]
            exact And.intro hn' hn
          have hn : n ≤ k := by
            rw [Nat.le_iff_lt_add_one]
            exact hn
          exact ih m n hm hn hmn

lemma embed_helper_order {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (m n : ℕ), I m < I n → @embed_helper _ _ hChain _ hI1 hI2 m < @embed_helper _ _ hChain _ hI1 hI2 n := by
  intro m n hmn
  exact embed_helper_order_helper (max m n) m n le_sup_left le_sup_right hmn

lemma embed_order_strict {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α), a < b → @embed _ _ hChain _ hI1 hI2 a < @embed _ _ hChain _ hI1 hI2 b := by
  intro a b hab
  unfold embed
  have ha : I (Function.invFun I a) = a := by
    apply Function.invFun_eq
    exact hI1.right a
  have hb : I (Function.invFun I b) = b := by
    apply Function.invFun_eq
    exact hI1.right b
  have hab : I (Function.invFun I a) < I (Function.invFun I b) := by
    rw [ha, hb]
    exact hab
  exact @embed_helper_order _ _ hChain _ hI1 hI2 (Function.invFun I a) (Function.invFun I b) hab

lemma embed_order {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α), a ≤ b → @embed _ _ hChain _ hI1 hI2 a ≤ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b hab
  by_cases hab' : a = b
  · rw [hab']
  · have hab : a < b := by simp [lt_iff_le_and_ne, hab, hab']
    simp [le_iff_eq_or_lt, embed_order_strict a b hab]

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

lemma embed_inf {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α ), @embed _ _ hChain _ hI1 hI2 (a ⊓ b) =
    @embed _ _ hChain _ hI1 hI2 a ⊓ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b
  by_cases h : a ≤ b
  · have h1 : @embed _ _ hChain _ hI1 hI2 a ≤ embed b := @embed_order _ _ _ _ hI1 hI2 a b h
    simp [h]
    exact h1
  · have h1 : b ≤ a := by
      have temp : a ≤ b ∨ b ≤ a := hChain a b
      by_contra
      have h2 : ¬a≤b ∧ ¬b≤a := And.intro h this
      rw [or_iff_not_and_not] at temp
      exact temp h2
    have h2 : @embed _ _ hChain _ hI1 hI2 b ≤ embed a := @embed_order _ _ _ _ hI1 hI2 b a h1
    simp [h1]
    exact h2

lemma embed_sup {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α ), @embed _ _ hChain _ hI1 hI2 (a ⊔ b) =
    @embed _ _ hChain _ hI1 hI2 a ⊔ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b
  by_cases h : a ≤ b
  · have h1 : @embed _ _ hChain _ hI1 hI2 a ≤ embed b := @embed_order _ _ _ _ hI1 hI2 a b h
    simp [h]
    exact h1
  · have h1 : b ≤ a := by
      have temp : a ≤ b ∨ b ≤ a := hChain a b
      by_contra
      have h2 : ¬a≤b ∧ ¬b≤a := And.intro h this
      rw [or_iff_not_and_not] at temp
      exact temp h2
    have h2 : @embed _ _ hChain _ hI1 hI2 b ≤ embed a := @embed_order _ _ _ _ hI1 hI2 b a h1
    simp [h1]
    exact h2

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

lemma embed_to {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} :
  ∀ (a b : α), @embed _ _ hChain _ hI1 hI2 (a ⇨ b) =
    @embed _ _ hChain _ hI1 hI2 a ⇨ @embed _ _ hChain _ hI1 hI2 b := by
  intro a b
  cases hChain a b
  · rename_i hab
    have h1 : @embed _ _ hChain _ hI1 hI2 a ≤ embed b := @embed_order _ _ _ _ hI1 hI2 a b hab
    have h2 : a ⇨ b = (⊤ : α) := by simp [hab]
    rw [h2]
    simp [himp, himp_Q]
    split_ifs
    · exact embed_top
  · rename_i hba
    rw [le_iff_lt_or_eq] at hba
    cases hba
    · rename_i hab
      have h1 : @embed _ _ hChain _ hI1 hI2 b < embed a := @embed_order_strict _ _ _ _ hI1 hI2 b a hab
      rw [lt_iff_le_not_ge] at hab
      simp [himp, himp_Q]
      have h2 : a ⇨ b = b := @chain_himp _ _ hChain a b hab.right
      rw [h2]
      have hEmbed : ¬ (@embed _ _ hChain _ hI1 hI2 a ≤ @embed _ _ hChain _ hI1 hI2 b) := by
        rw [not_le]
        exact h1
      split_ifs
      · rfl
    · rename_i hab
      have hab : a = b := by simp [hab]
      have hab : a ≤ b := by
        rw [le_iff_eq_or_lt]
        exact Or.inl hab
      have h1 : @embed _ _ hChain _ hI1 hI2 a ≤ embed b := @embed_order _ _ _ _ hI1 hI2 a b hab
      have h2 : a ⇨ b = (⊤ : α) := by simp [hab]
      rw [h2]
      simp [himp, himp_Q]
      split_ifs
      · exact embed_top

lemma embed_inj {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : Function.Injective (@embed _ _ hChain _ hI1 hI2) := by
  unfold Function.Injective
  intro a b hEmbed
  by_contra
  cases hChain a b
  · rename_i hab
    have hab : a < b := by
      rw [lt_iff_le_and_ne]
      exact And.intro hab this
    have hEmbed : @embed _ _ hChain _ hI1 hI2 a < embed b := @embed_order_strict _ _ _ _ hI1 hI2 a b hab
    rename_i temp _
    rw [lt_iff_le_and_ne] at hEmbed
    exact hEmbed.right temp
  · rename_i hab
    have this : ¬b=a := by
      apply Ne.symm
      exact this
    have hab : b < a := by
      rw [lt_iff_le_and_ne]
      exact And.intro hab this
    have hEmbed : @embed _ _ hChain _ hI1 hI2 b < embed a := @embed_order_strict _ _ _ _ hI1 hI2 b a hab
    rename_i temp _ _
    rw [lt_iff_le_and_ne] at hEmbed
    have temp : @embed _ _ hChain _ hI1 hI2 b = @embed _ _ hChain _ hI1 hI2 a := by
      apply Eq.symm
      exact temp
    exact hEmbed.right temp

lemma embed_homo {hChain : chain α} {I : ℕ → α} {hI1 : Function.Bijective I} {hI2 : I01 I} : Q_homomorphism (@embed _ _ hChain _ hI1 hI2) := by
  apply And.intro
  · exact embed_top
  · apply And.intro
    · exact embed_bot
    · intro _ _
      apply And.intro
      · exact @embed_order _ _ _ _ _ _ _ _
      · apply And.intro
        · exact @embed_inf _ _ _ _ _ _ _ _
        · apply And.intro
          · exact @embed_sup _ _ _ _ _ _ _ _
          · exact @embed_to _ _ _ _ _ _ _ _

-- The embedding into Q that we want exists
-- need a case for infinite and a case for finite
lemma embedding {hC : Countable α} : chain α → ∃ (f : α → Q), Q_homomorphism f ∧ Function.Injective f := by
  intro h1
  by_cases hInf : Infinite α
  · have hD : Denumerable α := @Denumerable.ofEncodableOfInfinite α (@Encodable.ofCountable α hC) hInf
    let enum1 := hD.eqv
    let σ1 := Equiv.swap 0 (enum1 ⊥)
    let σ2 := Equiv.swap (σ1 1) (enum1 ⊤)
    let σ := σ1.trans σ2
    let enum2 := hD.eqv.symm ∘ σ
    have h01 : enum2 0 = Bot.bot ∧ enum2 1 = Top.top := by
      simp [enum2, σ]
      apply And.intro
      · rw [Equiv.swap_apply_def]
        split_ifs
        · rename_i h
          unfold σ1 at h
          simp at h
          rw [Equiv.swap_apply_def] at h
          split_ifs at h
          · exfalso
            assumption
          · exfalso
            rename_i h' _ _
            simp at h'
          · exfalso
            rename_i h' _ _
            simp at h'
          · exfalso
            assumption
          · rename_i h'
            rw [h] at h'
            exfalso
            simp at h'
          · rename_i h'
            rw [h] at h'
            simp at h'
        · rename_i h
          rw [Equiv.swap_apply_left] at h
          have temp : (⊥ : α) = (⊤ : α) := enum1.injective h
          exfalso
          simp at temp
        · rw [Equiv.swap_apply_left]
          simp [enum1]
      · rw [Equiv.swap_apply_left]
        simp [enum1]
    have bij : enum2.Bijective := by
      rw [Equiv.comp_bijective]
      exact σ.bijective
    let f := @embed _ _ h1 enum2 bij h01
    have Qhomof : Q_homomorphism f := embed_homo
    have Injf : Function.Injective f := embed_inj
    exists f
  · sorry -- finite case (need to change previous definitions and lemmas to take a bijective function
          -- from a subset of ℕ that may be finite)

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
