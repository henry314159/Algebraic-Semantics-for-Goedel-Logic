import GoedelLogic.RationalUnitIntervalSoundness
import GoedelLogic.ChainCompleteness
import GoedelLogic.Formula
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Denumerable
import Mathlib.SetTheory.Cardinal.Finite

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

def S (N : WithTop ℕ) := {n : ℕ | n < N}

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
  have hy : (y : WithTop ℕ) < n := by simp [hy]
  exact lt_trans hy hn

instance range_equiv (N : WithTop ℕ) (n : S N) : range N n ≃ Fin n := {
  toFun := (fun x => ⟨x, mem_range N n x⟩)
  invFun := (fun y => ⟨⟨y, y_mem_S N n y y.isLt⟩, y.isLt⟩)
}

instance range_fin (N : WithTop ℕ) (n : S N) : Finite (range N n) := by
  rw [finite_iff_exists_equiv_fin]
  exists n
  apply Nonempty.intro
  exact range_equiv N n

lemma mem_S (N : WithTop ℕ) (n : ℕ) (hN : n < N) : n ∈ S N := by
  simp [S]
  exact hN

lemma mem_S' (N : WithTop ℕ) (n : ℕ) (x : ℕ) (hn : n < x) (hN : x < N) : n ∈ S N := by
  simp [S]
  have hn : (n : WithTop ℕ) < x := by simp [hn]
  exact lt_trans hn hN

variable {N : WithTop ℕ}
variable {hN : 1 < N}

def h01 (I : α → S N) : Prop :=
  I Bot.bot = ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ ∧
  I Top.top = ⟨1, mem_S N 1 hN⟩

lemma h01' (I : α → S N) (h : @h01 α _ N hN I) (bij : I.Bijective) :
  I.invFun ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ = Bot.bot ∧
  I.invFun ⟨1, mem_S N 1 hN⟩ = Top.top := by
  apply And.intro
  · have temp : I (I.invFun ⟨0, mem_S' N 0 1 zero_lt_one hN⟩) =
                ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ := by
      apply Function.invFun_eq
      exact bij.right ⟨0, mem_S' N 0 1 zero_lt_one hN⟩
    have temp' : I (I.invFun ⟨0, mem_S' N 0 1 zero_lt_one hN⟩) = I ⊥ := by
      rw [h.left]
      exact temp
    exact bij.left temp'
  · have temp : I (I.invFun ⟨1, mem_S N 1 hN⟩) =
                ⟨1, mem_S N 1 hN⟩ := by
      apply Function.invFun_eq
      exact bij.right ⟨1, mem_S N 1 hN⟩
    have temp' : I (I.invFun ⟨1, mem_S N 1 hN⟩) = I ⊤ := by
      rw [h.right]
      exact temp
    exact bij.left temp'

noncomputable def A (I : α → S N) (n : S N) : Finset α :=
  Finset.image I.invFun (@Set.toFinset (S N) (range N n) (Fintype.ofFinite (range N n)))

noncomputable instance decidable_lt (I : α → S N) (n : S N) :
  DecidablePred (fun a => a < I.invFun n) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h : a < I.invFun n
  · exact isTrue h
  · exact isFalse h

noncomputable instance decidable_gt (I : α → S N) (n : S N) :
  DecidablePred (fun a => I.invFun n < a) := by
  unfold DecidablePred
  intro a
  simp
  by_cases h : I.invFun n < a
  · exact isTrue h
  · exact isFalse h

noncomputable def B (I : α → S N) (n : S N) : Finset α :=
  (A I n).filter (fun a => a < I.invFun n)

lemma hB {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 (hN := hN) I} (n : S N) :
  ⟨1, mem_S N 1 hN⟩ < n → (B I n).Nonempty := by
  intro hn
  exists Bot.bot
  unfold B
  rw [Finset.mem_filter]
  apply And.intro
  · unfold A
    rw [Finset.mem_image]
    exists ⟨0, mem_S' N 0 1 zero_lt_one hN⟩
    apply And.intro
    · simp [range]
      have temp : (⟨0, mem_S' N 0 1 zero_lt_one hN⟩ : S N) <
                  ⟨1, mem_S N 1 hN⟩ := by simp
      exact lt_trans temp hn
    · have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
      have hbot : (I.invFun ∘ I) ⊥ = (⊥ : α) := by
        rw [hinv]
        rfl
      have hbot : I.invFun (I ⊥) = (⊥ : α) := hbot
      rw [←hbot]
      rw [hI2.left]
  · by_contra
    rw [not_bot_lt_iff] at this
    have this : I (I.invFun n) = I ⊥ := by rw [this]
    rw [hI2.left] at this
    have temp : I (I.invFun n) = n := by
      apply Function.invFun_eq
      exact bij.right n
    rw [this] at temp
    rw [←temp] at hn
    simp at hn

noncomputable def C {N : WithTop ℕ} (I : α → S N) (n : S N) : Finset α :=
  (A I n).filter (fun a => I.invFun n < a)

lemma hC {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 (hN := hN) I} (n : S N) :
  ⟨1, mem_S N 1 hN⟩ < n → (C I n).Nonempty := by
  intro hn
  exists Top.top
  unfold C
  rw [Finset.mem_filter]
  apply And.intro
  · unfold A
    rw [Finset.mem_image]
    exists ⟨1, mem_S N 1 hN⟩
    apply And.intro
    · simp [range]
      exact hn
    · have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
      have htop : (I.invFun ∘ I) ⊤ = (⊤ : α) := by
        rw [hinv]
        rfl
      have htop : I.invFun (I ⊤) = (⊤ : α) := htop
      rw [←htop]
      rw [hI2.right]
  · by_contra
    rw [not_lt_top_iff] at this
    have this : I (I.invFun n) = I ⊤ := by rw [this]
    rw [hI2.right] at this
    have temp : I (I.invFun n) = n := by
      apply Function.invFun_eq
      exact bij.right n
    rw [this] at temp
    rw [←temp] at hn
    simp at hn

noncomputable def ai {hChain : chain α} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 I} (n : S N) (hn : ⟨1, mem_S N 1 hN⟩ < n) :=
  @Finset.max' α (linear_order_chain (h := hChain)) (B I n) (@hB α _ N hN I bij hI2 n hn)

noncomputable def aj {hChain : chain α} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 I} (n : S N) (hn : ⟨1, mem_S N 1 hN⟩ < n) :=
  @Finset.min' α (linear_order_chain (h := hChain)) (C I n) (@hC α _ N hN I bij hI2 n hn)

lemma decreasing_ai {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 (hN := hN) I} (y : ℕ) (hy : y + 2 ∈ S N):
  @Subtype.val ℕ (fun x => x ∈ S N) (I (@ai α _ N hN hChain I bij hI2
  ⟨y + 2, hy⟩ (Nat.le_add_left 2 y))) < y.succ.succ := by
  let ai' := @ai α _ N hN hChain I bij hI2 ⟨y + 2, hy⟩ (Nat.le_add_left 2 y)
  have hai : ai' ∈ @A α _ N I ⟨y + 2, hy⟩ := by
    have haux : ai' ∈ @B α _ N I ⟨y + 2, hy⟩ :=
      @Finset.max'_mem α (@linear_order_chain α _ hChain)
                          (@B α _ N I ⟨y + 2, hy⟩)
                          (@hB α _ N hN I bij hI2 ⟨y + 2, hy⟩ (Nat.le_add_left 2 y))
    unfold B at haux
    rw [@Finset.mem_filter α (fun a => a < I.invFun ⟨y + 2, hy⟩)
        (@decidable_lt α _ N I ⟨y + 2, hy⟩)
        (@A α _ N I ⟨y + 2, hy⟩) ai'] at haux
    exact haux.left
  unfold A at hai
  rw [@Finset.mem_image (S N) α _ I.invFun
      (@Set.toFinset (S N) (range N (y + 2))
      (@Fintype.ofFinite (range N (y+2)) (range_fin N ⟨y + 2, hy⟩))) ai'] at hai
  obtain ⟨a, ha1, ha2⟩ := hai
  have ha2 : I (I.invFun a) = I ai' := by rw [ha2]
  have temp : I (I.invFun a) = a := by
    apply Function.invFun_eq
    exact bij.right a
  rw [temp] at ha2
  rw [←ha2]
  simp [range] at ha1
  exact ha1

lemma decreasing_aj {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 (hN := hN) I} (y : ℕ) (hy : y + 2 ∈ S N):
  @Subtype.val ℕ (fun x => x ∈ S N) (I (@aj α _ N hN hChain I bij hI2
  ⟨y + 2, hy⟩ (Nat.le_add_left 2 y))) < y.succ.succ := by
  let aj' := @aj α _ N hN hChain I bij hI2 ⟨y + 2, hy⟩ (Nat.le_add_left 2 y)
  have haj : aj' ∈ @A α _ N I ⟨y + 2, hy⟩ := by
    have haux : aj' ∈ @C α _ N I ⟨y + 2, hy⟩ :=
      @Finset.min'_mem α (@linear_order_chain α _ hChain)
                          (@C α _ N I ⟨y + 2, hy⟩)
                          (@hC α _ N hN I bij hI2 ⟨y + 2, hy⟩ (Nat.le_add_left 2 y))
    unfold C at haux
    rw [@Finset.mem_filter α (fun a => I.invFun ⟨y + 2, hy⟩ < a)
        (@decidable_gt α _ N I ⟨y + 2, hy⟩)
        (@A α _ N I ⟨y + 2, hy⟩) aj'] at haux
    exact haux.left
  unfold A at haj
  rw [@Finset.mem_image (S N) α _ I.invFun
      (@Set.toFinset (S N) (range N (y + 2))
      (@Fintype.ofFinite (range N (y+2)) (range_fin N ⟨y + 2, hy⟩))) aj'] at haj
  obtain ⟨a, ha1, ha2⟩ := haj
  have ha2 : I (I.invFun a) = I aj' := by rw [ha2]
  have temp : I (I.invFun a) = a := by
    apply Function.invFun_eq
    exact bij.right a
  rw [temp] at ha2
  rw [←ha2]
  simp [range] at ha1
  exact ha1

noncomputable def embed_helper {hChain : chain α} {I : α → S N} {bij: I.Bijective}
  {hI2 : h01 (hN := hN) I} (n : S N) : Q :=
  match n with
  | ⟨0, _⟩ => ⟨0, zero_mem_Q⟩
  | ⟨1, _⟩ => ⟨1, one_mem_Q⟩
  | ⟨y + 2, y_succ_succ_mem_S⟩ =>
      mean (@embed_helper hChain I bij hI2 (I (@ai α _ N hN hChain I bij hI2
            ⟨y + 2, y_succ_succ_mem_S⟩ (Nat.le_add_left 2 y))))
           (@embed_helper hChain I bij hI2 (I (@aj α _ N hN hChain I bij hI2
            ⟨y + 2, y_succ_succ_mem_S⟩ (Nat.le_add_left 2 y))))
  decreasing_by
    · unfold sizeOf
      unfold Subtype._sizeOf_inst
      unfold Subtype._sizeOf_1
      simp only [sizeOf_nat, sizeOf_default, add_zero, add_lt_add_iff_left]
      exact @decreasing_ai α _ N hN hChain I bij hI2 y y_succ_succ_mem_S
    · unfold sizeOf
      unfold Subtype._sizeOf_inst
      unfold Subtype._sizeOf_1
      simp only [sizeOf_nat, sizeOf_default, add_zero, add_lt_add_iff_left]
      exact @ decreasing_aj α _ N hN hChain I bij hI2 y y_succ_succ_mem_S

noncomputable def embed {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 (hN := hN) I} (a : α) : Q :=
  @embed_helper α _ N hN hChain I bij hI2 (I a)

lemma embed_top {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  @embed α _ N hN hChain I bij hI2 Top.top = Top.top := by
  rw [embed, hI2.right, embed_helper]
  rfl

lemma embed_bot {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  @embed α _ N hN hChain I bij hI2 Bot.bot = Bot.bot := by
  rw [embed, hI2.left, embed_helper]
  rfl

lemma embed_helper_order_helper {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  ∀ (k : ℕ), ∀ (m n : S N), m.val ≤ k → n.val ≤ k → I.invFun m < I.invFun n →
    @embed_helper α _ N hN hChain I bij hI2 m <
    @embed_helper α _ N hN hChain I bij hI2 n := by
  intro k
  induction k with
  | zero =>
      intro m n hm hn hI
      exfalso
      have hm : m = ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ := by
        obtain ⟨_, _⟩ := m
        simp
        simp at hm
        exact hm
      have hn : n = ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ := by
        obtain ⟨_, _⟩ := n
        simp
        simp at hn
        exact hn
      rw [hm, hn] at hI
      rw [← @lt_self_iff_false α]
      exact hI
  | succ k ih =>
      intro m n
      obtain ⟨m, hm⟩ := m
      obtain ⟨n, hn⟩ := n
      by_cases hk : k + 1 < N
      · by_cases hm' : m = k + 1
        · by_cases hn' : n = k + 1
          · intro _ _ hI
            have hm' : (⟨m, hm⟩ : S N) = ⟨k + 1, hk⟩ := by simp [hm']
            have hn' : (⟨n, hn⟩ : S N) = ⟨k + 1, hk⟩ := by simp [hn']
            rw [hm', hn'] at hI
            exfalso
            rw [← @lt_self_iff_false α]
            exact hI
          · intro hm'' hn'' hmn
            have hn''' : n < k + 1 := by
              rw [lt_iff_le_and_ne]
              exact And.intro hn'' hn'
            have hn''' : n ≤ k := by
              rw [Nat.le_iff_lt_add_one]
              exact hn'''
            unfold embed_helper
            split
            · exfalso
              rename_i hm0
              rw [hm0] at hmn
              simp at hm0
              rw [hm0] at hm'
              have hntemp : n = 0 := by
                rw [← hm'] at hn''
                rw [← Nat.le_zero]
                exact hn''
              rw [← hm'] at hn'
              exact hn' hntemp
            · exfalso
              rename_i hm1
              simp at hm1
              rw [hm1] at hm'
              have hk : k = 0 := by
                rw [← right_eq_add]
                exact hm'
              have hntemp : n = 0 := by
                rw [hk] at hn'''
                rw [← Nat.le_zero]
                exact hn'''
              have hntemp : @Subtype.mk ℕ (fun x => x ∈ S N) n hn = ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ := by simp [hntemp]
              have hmtemp : @Subtype.mk ℕ (fun x => x ∈ S N) m hm = ⟨1, mem_S N 1 hN⟩ := by simp [hm1]
              rw [hntemp, hmtemp] at hmn
              rw [(@h01' α _ N hN I hI2 bij).left] at hmn
              rw [(@h01' α _ N hN I hI2 bij).right] at hmn
              exact not_lt_bot hmn
            · split
              · exfalso
                rename_i hn
                rw [hn] at hmn
                rw [(@h01' α _ N hN I hI2 bij).left] at hmn
                exact not_lt_bot hmn
              · rw [lt_iff_le_and_ne]
                apply And.intro
                · exact le_top
                · by_contra
                  rename_i y hy hmy _ _ hntemp
                  rw [mean_eq_one] at this
                  let ai' := @ai α _ N hN hChain I bij hI2 ⟨y.succ.succ, hy⟩ (embed_helper._proof_5 y)
                  have hai1 : ai' < I.invFun ⟨y.succ.succ, hy⟩ := by
                    have haux : ai' ∈ B I ⟨y.succ.succ, hy⟩ :=
                      @Finset.max'_mem α (@linear_order_chain α _ hChain)
                      (B I ⟨y.succ.succ, hy⟩)
                      (@hB α _ N hN I bij hI2 ⟨y.succ.succ, hy⟩ (Nat.le_add_left 2 y))
                    unfold B at haux
                    rw [@Finset.mem_filter α (fun a => a < I.invFun ⟨y.succ.succ, hy⟩)
                        (@decidable_lt α _ N I ⟨y.succ.succ, hy⟩)
                        (A I ⟨y.succ.succ, hy⟩) ai'] at haux
                    exact haux.right
                  rw [hmy, hntemp] at hmn
                  have hai1 : ai' < I.invFun ⟨1, mem_S N 1 hN⟩ :=
                    lt_trans hai1 hmn
                  have hai1 : I.invFun (I ai') < I.invFun ⟨1, mem_S N 1 hN⟩ := by
                    have temp : I.invFun (I ai') = ai' := by
                      have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
                      have hinv : (I.invFun ∘ I) ai' = ai' := by
                        rw [hinv]
                        rfl
                      exact hinv
                    rw [temp]
                    exact hai1
                  have hai2 : @Subtype.val ℕ (fun x => x ∈ S N) (I ai') < y.succ.succ :=
                    @decreasing_ai α _ N hN hChain I bij hI2 y hy
                  have hai2 : (I ai' : WithTop ℕ) ≤ (k : WithTop ℕ) := by
                    simp
                    simp only [Subtype.mk.injEq] at hmy
                    rw [hmy] at hm'
                    rw [hm'] at hai2
                    rw [← Nat.lt_add_one_iff]
                    exact hai2
                  have hai2 : I ai' ≤ k := by
                    simp at hai2
                    exact hai2
                  simp at hntemp
                  rw [hntemp] at hn'''
                  have hai3 : @embed_helper α _ N hN hChain I bij hI2 (I ai') <
                              @embed_helper α _ N hN hChain I bij hI2 ⟨1, mem_S N 1 hN⟩ :=
                    ih (I ai') ⟨1, mem_S N 1 hN⟩ hai2 hn''' hai1
                  have temp : @embed α _ N hN hChain I bij hI2 (⊤ : α) =
                              @embed_helper α _ N hN hChain I bij hI2 ⟨1, mem_S N 1 hN⟩ := by
                    unfold embed
                    rw [←(@h01' α _ N hN I hI2 bij).right]
                    have temp : I (I.invFun ⟨1, mem_S N 1 hN⟩) = ⟨1, mem_S N 1 hN⟩ := by
                      apply Function.invFun_eq
                      exact bij.right ⟨1, mem_S N 1 hN⟩
                    rw [temp]
                  rw [← temp, embed_top] at hai3
                  rw [lt_iff_le_and_ne] at hai3
                  exact hai3.right this.left
              · rename_i n1 y1 hy1 hmtemp n2 y2 hy2 hntemp
                let ai1 := @ai α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ (Nat.le_add_left 2 y1)
                let aj1 := @aj α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ (Nat.le_add_left 2 y1)
                let ai2 := @ai α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ (Nat.le_add_left 2 y2)
                let aj2 := @aj α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ (Nat.le_add_left 2 y2)
                have temp1 : @embed_helper α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ =
                       mean (@embed_helper α _ N hN hChain I bij hI2 (I ai1))
                            (@embed_helper α _ N hN hChain I bij hI2 (I aj1)) := by
                  rw [embed_helper]
                have temp2 : @embed_helper α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ =
                       mean (@embed_helper α _ N hN hChain I bij hI2 (I ai2))
                            (@embed_helper α _ N hN hChain I bij hI2 (I aj2)) := by
                  rw [embed_helper]
                simp only [ai1, aj1, ai2, aj2, ← temp1, ← temp2]
                have h1 : @Subtype.val ℕ (fun x => x ∈ S N) (I aj1) < y1.succ.succ :=
                    @decreasing_aj α _ N hN hChain I bij hI2 y1 hy1
                have h1 : (I aj1 : WithTop ℕ) ≤ (k : WithTop ℕ) := by
                  simp
                  simp only [Subtype.mk.injEq] at hmtemp
                  rw [hmtemp] at hm'
                  rw [hm'] at h1
                  rw [← Nat.lt_add_one_iff]
                  exact h1
                have h1 : I aj1 ≤ k := by
                  simp at h1
                  exact h1
                have h2 : aj1 ≤ I.invFun ⟨y2.succ.succ, hy2⟩ := by
                  have temp : I.invFun ⟨y2.succ.succ, hy2⟩ ∈
                              C I ⟨y1.succ.succ, hy1⟩ := by
                    unfold C
                    rw [@Finset.mem_filter α (fun a => I.invFun ⟨y1.succ.succ, hy1⟩ < a)
                        (@decidable_gt α _ N I ⟨y1.succ.succ, hy1⟩)
                        (A I ⟨y1.succ.succ, hy1⟩)
                        (I.invFun ⟨y2.succ.succ, hy2⟩)]
                    apply And.intro
                    · unfold A
                      unfold range
                      simp only [Set.coe_setOf, Finset.mem_image, Set.mem_toFinset, Set.mem_setOf_eq, Subtype.exists, exists_and_left]
                      exists y2.succ.succ
                      apply And.intro
                      · rename_i temp _ _
                        rw [← hm'] at temp
                        simp at hntemp
                        simp at hmtemp
                        rw [hmtemp, hntemp] at temp
                        exact temp
                      · exists hy2
                    · rw [hmtemp, hntemp] at hmn
                      exact hmn
                  exact @Finset.min'_le α (@linear_order_chain α _ hChain)
                        (C I ⟨y1.succ.succ, hy1⟩)
                        (I.invFun ⟨y2.succ.succ, hy2⟩) temp
                have h2 : I.invFun (I aj1) ≤ I.invFun ⟨y2.succ.succ, hy2⟩ := by
                  have temp : I.invFun (I aj1) = aj1 := by
                    have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
                    have hinv : (I.invFun ∘ I) aj1 = aj1 := by
                      rw [hinv]
                      rfl
                    exact hinv
                  rw [temp]
                  exact h2
                have h3 : @embed_helper α _ N hN hChain I bij hI2 (I aj1) ≤
                          @embed_helper α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ := by
                  by_cases htemp : I aj1 = ⟨y2.succ.succ, hy2⟩
                  · rw [htemp]
                  · rw [le_iff_lt_or_eq]
                    simp at hntemp
                    rw [hntemp] at hn'''
                    have temp : Function.invFun I (I aj1) ≠ Function.invFun I ⟨y2.succ.succ, hy2⟩ := by
                      by_contra
                      have this : I (I.invFun (I aj1)) = I (I.invFun (⟨y2.succ.succ, hy2⟩)) := by
                        rw [this]
                      have hleft : I (I.invFun (I aj1)) = I aj1 := by
                        apply Function.invFun_eq
                        exists aj1
                      have hright : I (I.invFun ⟨y2.succ.succ, hy2⟩) = ⟨y2.succ.succ, hy2⟩ := by
                        apply Function.invFun_eq
                        exact bij.right ⟨y2.succ.succ, hy2⟩
                      rw [hleft, hright] at this
                      exact htemp this
                    have temp : Function.invFun I (I aj1) < Function.invFun I ⟨y2.succ.succ, hy2⟩ := by
                      rw [lt_iff_le_and_ne]
                      exact And.intro h2 temp
                    exact Or.inl (ih (I aj1) ⟨y2.succ.succ, hy2⟩ h1 hn''' temp)
                have h4 : @Subtype.val ℕ (fun x => x ∈ S N) (I ai1) < y1.succ.succ :=
                    @decreasing_ai α _ N hN hChain I bij hI2 y1 hy1
                have h4 : (I ai1 : WithTop ℕ) ≤ (k : WithTop ℕ) := by
                  simp
                  simp only [Subtype.mk.injEq] at hmtemp
                  rw [hmtemp] at hm'
                  rw [hm'] at h4
                  rw [← Nat.lt_add_one_iff]
                  exact h4
                have h4 : I ai1 ≤ k := by
                  simp at h4
                  exact h4
                have h5 : ai1 < I.invFun ⟨y1.succ.succ, hy1⟩ := by
                  have haux : ai1 ∈ B I ⟨y1.succ.succ, hy1⟩ :=
                    @Finset.max'_mem α (@linear_order_chain α _ hChain)
                    (B I ⟨y1.succ.succ, hy1⟩)
                    (@hB α _ N hN I bij hI2 ⟨y1.succ.succ, hy1⟩ (Nat.le_add_left 2 y1))
                  unfold B at haux
                  rw [@Finset.mem_filter α (fun a => a < I.invFun ⟨y1.succ.succ, hy1⟩)
                      (@decidable_lt α _ N I ⟨y1.succ.succ, hy1⟩)
                      (A I ⟨y1.succ.succ, hy1⟩) ai1] at haux
                  exact haux.right
                have h5 : I.invFun (I ai1) < I.invFun ⟨y1.succ.succ, hy1⟩ := by
                  have temp : I.invFun (I ai1) = ai1 := by
                    have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
                    have hinv : (I.invFun ∘ I) ai1 = ai1 := by
                      rw [hinv]
                      rfl
                    exact hinv
                  rw [temp]
                  exact h5
                rw [hmtemp, hntemp] at hmn
                have h6 : I.invFun (I ai1) < I.invFun ⟨y2.succ.succ, hy2⟩ := lt_trans h5 hmn
                simp at hntemp
                rw [hntemp] at hn'''
                have h7 : @embed_helper α _ N hN hChain I bij hI2 (I ai1) <
                          @embed_helper α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ :=
                  ih (I ai1) ⟨y2.succ.succ, hy2⟩ h4 hn''' h6
                have h8 : mean (embed ai1) (embed aj1) < embed_helper ⟨y2.succ.succ, hy2⟩ :=
                  mean_lt (@embed α _ N hN hChain I bij hI2 ai1)
                          (@embed α _ N hN hChain I bij hI2 aj1)
                          (@embed_helper α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩)
                          h7 h3
                rw [temp1]
                simp only [embed] at h8
                exact h8
        · by_cases hn' : n = k + 1
          · intro hm'' hn'' hmn
            have hm''' : m < k + 1 := by
              rw [lt_iff_le_and_ne]
              exact And.intro hm'' hm'
            have hm''' : m ≤ k := by
              rw [Nat.le_iff_lt_add_one]
              exact hm'''
            unfold embed_helper
            split
            · split
              · exfalso
                rename_i hn
                rw [hn] at hmn
                rw [(@h01' α _ N hN I hI2 bij).left] at hmn
                exact not_lt_bot hmn
              · simp
              · rw [lt_iff_le_and_ne]
                apply And.intro
                · exact bot_le
                · apply Ne.symm
                  by_contra
                  rename_i hmtemp _ y hy hntemp
                  rw [mean_eq_zero] at this
                  let aj' := @aj α _ N hN hChain I bij hI2
                             ⟨y.succ.succ, hy⟩ (embed_helper._proof_5 y)
                  have haj1 : I.invFun ⟨y.succ.succ, hy⟩ < aj' := by
                    have haux : aj' ∈ C I ⟨y.succ.succ, hy⟩ :=
                      @Finset.min'_mem α (@linear_order_chain α _ hChain)
                      (C I ⟨y.succ.succ, hy⟩)
                      (@hC α _ N hN I bij hI2 ⟨y.succ.succ, hy⟩ (Nat.le_add_left 2 y))
                    unfold C at haux
                    rw [@Finset.mem_filter α (fun a => I.invFun ⟨y.succ.succ, hy⟩ < a)
                        (@decidable_gt α _ N I ⟨y.succ.succ, hy⟩)
                        (A I ⟨y.succ.succ, hy⟩) aj'] at haux
                    exact haux.right
                  rw [hmtemp, hntemp] at hmn
                  have haj1 : I.invFun ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ < aj' :=
                    lt_trans hmn haj1
                  have haj1 : I.invFun ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ < I.invFun (I aj') := by
                    have temp : I.invFun (I aj') = aj' := by
                      have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
                      have hinv : (I.invFun ∘ I) aj' = aj' := by
                        rw [hinv]
                        rfl
                      exact hinv
                    rw [temp]
                    exact haj1
                  have haj2 : @Subtype.val ℕ (fun x => x ∈ S N) (I aj') < y.succ.succ :=
                    @decreasing_aj α _ N hN hChain I bij hI2 y hy
                  have haj2 : (I aj' : WithTop ℕ) ≤ (k : WithTop ℕ) := by
                    simp
                    simp only [Subtype.mk.injEq] at hntemp
                    rw [hntemp] at hn'
                    rw [hn'] at haj2
                    rw [← Nat.lt_add_one_iff]
                    exact haj2
                  have haj2 : I aj' ≤ k := by
                    simp at haj2
                    exact haj2
                  simp at hmtemp
                  rw [hmtemp] at hm'''
                  have haj3 : @embed_helper α _ N hN hChain I bij hI2 ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ <
                              @embed_helper α _ N hN hChain I bij hI2 (I aj') :=
                    ih ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ (I aj') hm''' haj2 haj1
                  have temp : @embed α _ N hN hChain I bij hI2 (⊥ : α) =
                              @embed_helper α _ N hN hChain I bij hI2 ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ := by
                    unfold embed
                    rw [←(@h01' α _ N hN I hI2 bij).left]
                    have temp : I (I.invFun ⟨0, mem_S' N 0 1 zero_lt_one hN⟩) = ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ := by
                      apply Function.invFun_eq
                      exact bij.right ⟨0, mem_S' N 0 1 zero_lt_one hN⟩
                    rw [temp]
                  rw [← temp, embed_bot] at haj3
                  rw [lt_iff_le_and_ne] at haj3
                  exact haj3.right this.right.symm
            · exfalso
              rename_i hm1
              have hmtemp : @Subtype.mk ℕ (fun x => x ∈ S N) m hm = ⟨1, mem_S N 1 hN⟩ := by simp [hm1]
              rw [hm1] at hmn
              rw [(@h01' α _ N hN I hI2 bij).right] at hmn
              exact not_top_lt hmn
            · split
              · exfalso
                rename_i hn0
                have hntemp : @Subtype.mk ℕ (fun x => x ∈ S N) n hn = ⟨0, mem_S' N 0 1 zero_lt_one hN⟩ := by simp [hn0]
                rw [hntemp] at hmn
                rw [(@h01' α _ N hN I hI2 bij).left] at hmn
                exact not_lt_bot hmn
              · exfalso
                rename_i hmtemp _ _ _ hmy _ _ hntemp
                simp at hntemp
                rw [hntemp] at hn'
                rw [←hn'] at hmtemp
                simp at hmy
                rw [hmy] at hmtemp
                simp at hmtemp
              · rename_i n1 y1 hy1 hmtemp n2 y2 hy2 hntemp
                let ai1 := @ai α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ (Nat.le_add_left 2 y1)
                let aj1 := @aj α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ (Nat.le_add_left 2 y1)
                let ai2 := @ai α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ (Nat.le_add_left 2 y2)
                let aj2 := @aj α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ (Nat.le_add_left 2 y2)
                have temp1 : @embed_helper α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ =
                       mean (@embed_helper α _ N hN hChain I bij hI2 (I ai1))
                            (@embed_helper α _ N hN hChain I bij hI2 (I aj1)) := by
                  rw [embed_helper]
                have temp2 : @embed_helper α _ N hN hChain I bij hI2 ⟨y2.succ.succ, hy2⟩ =
                       mean (@embed_helper α _ N hN hChain I bij hI2 (I ai2))
                            (@embed_helper α _ N hN hChain I bij hI2 (I aj2)) := by
                  rw [embed_helper]
                simp only [ai1, aj1, ai2, aj2, ← temp1, ← temp2]
                have h1 : I.invFun ⟨y1.succ.succ, hy1⟩ ≤ ai2 := by
                  have temp : I.invFun ⟨y1.succ.succ, hy1⟩ ∈ B I ⟨y2.succ.succ, hy2⟩ := by
                    unfold B
                    rw [@Finset.mem_filter α (fun a => a < I.invFun ⟨y2.succ.succ, hy2⟩)
                        (@decidable_lt α _ N I ⟨y2.succ.succ, hy2⟩)
                        (A I ⟨y2.succ.succ, hy2⟩)
                        (I.invFun ⟨y1.succ.succ, hy1⟩)]
                    apply And.intro
                    · unfold A
                      simp [range]
                      exists y1.succ.succ
                      apply And.intro
                      · rename_i temp
                        rw [← hn'] at temp
                        simp at hmtemp
                        simp at hntemp
                        rw [hmtemp, hntemp] at temp
                        exact temp
                      · exists hy1
                    · rw [hmtemp, hntemp] at hmn
                      exact hmn
                  exact @Finset.le_max' α (@linear_order_chain α _ hChain)
                        (B I ⟨y2.succ.succ, hy2⟩)
                        (I.invFun ⟨y1.succ.succ, hy1⟩) temp
                have h1 : I.invFun ⟨y1.succ.succ, hy1⟩ ≤ I.invFun (I ai2) := by
                  have temp : I.invFun (I ai2) = ai2 := by
                    have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
                    have hinv : (I.invFun ∘ I) ai2 = ai2 := by
                      rw [hinv]
                      rfl
                    exact hinv
                  rw [temp]
                  exact h1
                have h2 : I ai2 < y2.succ.succ :=
                  @decreasing_ai α _ N hN hChain I bij hI2 y2 hy2
                have h2 : (I ai2 : WithTop ℕ) ≤ (k : WithTop ℕ) := by
                  simp
                  simp only [Subtype.mk.injEq] at hntemp
                  rw [hntemp] at hn'
                  rw [hn'] at h2
                  rw [← Nat.lt_add_one_iff]
                  exact h2
                have h2 : I ai2 ≤ k := by
                  simp at h2
                  exact h2
                have h3 : @embed_helper α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ ≤
                          @embed_helper α _ N hN hChain I bij hI2 (I ai2) := by
                  by_cases htemp : ⟨y1.succ.succ, hy1⟩ = I ai2
                  · rw [htemp]
                  · rw [le_iff_lt_or_eq]
                    simp at hmtemp
                    rw [hmtemp] at hm'''
                    have temp : Function.invFun I ⟨y1.succ.succ, hy1⟩ ≠ Function.invFun I (I ai2) := by
                      by_contra
                      have this : I (I.invFun ⟨y1.succ.succ, hy1⟩) = I (I.invFun (I ai2)) := by
                        rw [this]
                      have hleft : I (I.invFun ⟨y1.succ.succ, hy1⟩) = ⟨y1.succ.succ, hy1⟩ := by
                        apply Function.invFun_eq
                        exact bij.right ⟨y1.succ.succ, hy1⟩
                      have hright : I (I.invFun (I ai2)) = I ai2 := by
                        apply Function.invFun_eq
                        exists ai2
                      rw [hleft, hright] at this
                      exact htemp this
                    have temp : Function.invFun I ⟨y1.succ.succ, hy1⟩ < Function.invFun I (I ai2) := by
                      rw [lt_iff_le_and_ne]
                      exact And.intro h1 temp
                    exact Or.inl (ih ⟨y1.succ.succ, hy1⟩ (I ai2) hm''' h2 temp)
                have h4 : I.invFun ⟨y1.succ.succ, hy1⟩ < aj2 := by
                  have htemp : I.invFun ⟨y2.succ.succ, hy2⟩ < aj2 := by
                    have haj2 : aj2 ∈ C I ⟨y2.succ.succ, hy2⟩ :=
                      @Finset.min'_mem α (@linear_order_chain α _ hChain)
                      (C I ⟨y2.succ.succ, hy2⟩)
                      (@hC α _ N hN I bij hI2 ⟨y2.succ.succ, hy2⟩ (Nat.le_add_left 2 y2))
                    unfold C at haj2
                    rw [@Finset.mem_filter α (fun a => I.invFun ⟨y2.succ.succ, hy2⟩ < a)
                        (@decidable_gt α _ N I ⟨y2.succ.succ, hy2⟩)
                        (A I ⟨y2.succ.succ, hy2⟩) aj2] at haj2
                    exact haj2.right
                  rw [hmtemp, hntemp] at hmn
                  exact lt_trans hmn htemp
                have h4 : I.invFun ⟨y1.succ.succ, hy1⟩ < I.invFun (I aj2) := by
                  have temp : I.invFun (I aj2) = aj2 := by
                    have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
                    have hinv : (I.invFun ∘ I) aj2 = aj2 := by
                      rw [hinv]
                      rfl
                    exact hinv
                  rw [temp]
                  exact h4
                have h5 : @Subtype.val ℕ (fun x => x ∈ S N) (I aj2) < y2.succ.succ :=
                  @decreasing_aj α _ N hN hChain I bij hI2 y2 hy2
                have h5 : (I aj2 : WithTop ℕ) ≤ (k : WithTop ℕ) := by
                  simp
                  simp only [Subtype.mk.injEq] at hntemp
                  rw [hntemp] at hn'
                  rw [hn'] at h5
                  rw [← Nat.lt_add_one_iff]
                  exact h5
                have h5 : I aj2 ≤ k := by
                  simp at h5
                  exact h5
                simp at hmtemp
                rw [hmtemp] at hm'''
                have h6 : @embed_helper α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩ <
                          @embed_helper α _ N hN hChain I bij hI2 (I aj2) :=
                  ih ⟨y1.succ.succ, hy1⟩ (I aj2) hm''' h5 h4
                have h7 : embed_helper ⟨y1.succ.succ, hy1⟩ < mean (embed ai2) (embed aj2) :=
                  lt_mean (@embed_helper α _ N hN hChain I bij hI2 ⟨y1.succ.succ, hy1⟩)
                          (@embed α _ N hN hChain I bij hI2 ai2)
                          (@embed α _ N hN hChain I bij hI2 aj2)
                          h3 h6
                rw [temp2]
                simp only [embed] at h7
                exact h7
          · intro hm'' hn'' hmn
            have hm''' : m < k + 1 := by
              rw [lt_iff_le_and_ne]
              exact And.intro hm'' hm'
            have hm''' : m ≤ k := by
              rw [Nat.le_iff_lt_add_one]
              exact hm'''
            have hn''' : n < k + 1 := by
              rw [lt_iff_le_and_ne]
              exact And.intro hn'' hn'
            have hn''' : n ≤ k := by
              rw [Nat.le_iff_lt_add_one]
              exact hn'''
            exact ih ⟨m, hm⟩ ⟨n, hn⟩ hm''' hn''' hmn
      · simp at hk
        have hmk : (m : WithTop ℕ) < (k : WithTop ℕ) + 1 := lt_of_lt_of_le hm hk
        have hmk : (m : WithTop ℕ) ≤ (k : WithTop ℕ) := by
          rw [Nat.cast_le]
          rw [Nat.le_iff_lt_add_one]
          rw [← WithTop.coe_lt_coe]
          exact hmk
        have hm' : @Subtype.val ℕ (fun x => x ∈ S N) ⟨m, hm⟩ ≤ k := by
          rw [← WithTop.coe_le_coe]
          exact hmk
        have hnk : (n : WithTop ℕ) < (k : WithTop ℕ) + 1 := lt_of_lt_of_le hn hk
        have hnk : (n : WithTop ℕ) ≤ (k : WithTop ℕ) := by
          rw [Nat.cast_le]
          rw [Nat.le_iff_lt_add_one]
          rw [← WithTop.coe_lt_coe]
          exact hnk
        have hn' : @Subtype.val ℕ (fun x => x ∈ S N) ⟨n, hn⟩ ≤ k := by
          rw [← WithTop.coe_le_coe]
          exact hnk
        intro _ _ h
        exact ih ⟨m, hm⟩ ⟨n, hn⟩ hm' hn' h

lemma embed_helper_order {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  ∀ (m n : S N), I.invFun m < I.invFun n →
    @embed_helper α _ N hN hChain I bij hI2 m <
    @embed_helper α _ N hN hChain I bij hI2 n := by
    intro m n hmn
    exact embed_helper_order_helper (max m n) m n le_sup_left le_sup_right hmn

lemma embed_order_strict {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  ∀ (a b : α), a < b →
  @embed α _ N hN hChain I bij hI2 a <
  @embed α _ N hN hChain I bij hI2 b := by
  intro a b hab
  unfold embed
  have hinv : I.invFun ∘ I = id := Function.invFun_comp bij.left
  have ha : (I.invFun ∘ I) a = a := by
    rw [hinv]
    rfl
  have ha : I.invFun (I a) = a := ha
  have hb : (I.invFun ∘ I) b = b := by
    rw [hinv]
    rfl
  have hb : I.invFun (I b) = b := hb
  have hab : I.invFun (I a) < I.invFun (I b) := by
    rw [ha, hb]
    exact hab
  exact @embed_helper_order _ _ N hN hChain I bij hI2 (I a) (I b) hab

lemma embed_order {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  ∀ (a b : α), a ≤ b →
  @embed α _ N hN hChain I bij hI2 a ≤
  @embed α _ N hN hChain I bij hI2 b := by
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

lemma embed_inf {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  ∀ (a b : α),
  @embed α _ N hN hChain I bij hI2 (a ⊓ b) =
  @embed α _ N hN hChain I bij hI2 a ⊓
  @embed α _ N hN hChain I bij hI2 b := by
  intro a b
  by_cases h : a ≤ b
  · have h1 : @embed α _ N hN hChain I bij hI2 a ≤
              embed b :=
              @embed_order α _ N hN hChain I bij hI2 a b h
    simp [h]
    exact h1
  · have h1 : b ≤ a := by
      have temp : a ≤ b ∨ b ≤ a := hChain a b
      by_contra
      have h2 : ¬a≤b ∧ ¬b≤a := And.intro h this
      rw [or_iff_not_and_not] at temp
      exact temp h2
    have h2 : @embed α _ N hN hChain I bij hI2 b ≤
              embed a :=
              @embed_order α _ N hN hChain I bij hI2 b a h1
    simp [h1]
    exact h2

lemma embed_sup {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  ∀ (a b : α),
  @embed α _ N hN hChain I bij hI2 (a ⊔ b) =
  @embed α _ N hN hChain I bij hI2 a ⊔
  @embed α _ N hN hChain I bij hI2 b := by
  intro a b
  by_cases h : a ≤ b
  · have h1 : @embed α _ N hN hChain I bij hI2 a ≤
              embed b :=
              @embed_order α _ N hN hChain I bij hI2 a b h
    simp [h]
    exact h1
  · have h1 : b ≤ a := by
      have temp : a ≤ b ∨ b ≤ a := hChain a b
      by_contra
      have h2 : ¬a≤b ∧ ¬b≤a := And.intro h this
      rw [or_iff_not_and_not] at temp
      exact temp h2
    have h2 : @embed α _ N hN hChain I bij hI2 b ≤
              embed a :=
              @embed_order α _ N hN hChain I bij hI2 b a h1
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

lemma embed_to {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  ∀ (a b : α),
  @embed α _ N hN hChain I bij hI2 (a ⇨ b) =
  @embed α _ N hN hChain I bij hI2 a ⇨
  @embed α _ N hN hChain I bij hI2 b := by
  intro a b
  cases hChain a b
  · rename_i hab
    have h1 : @embed α _ N hN hChain I bij hI2 a ≤
              embed b :=
              @embed_order α _ N hN hChain I bij hI2 a b hab
    have h2 : a ⇨ b = (⊤ : α) := by simp [hab]
    rw [h2]
    simp [himp, himp_Q]
    split_ifs
    · exact embed_top
  · rename_i hba
    rw [le_iff_lt_or_eq] at hba
    cases hba
    · rename_i hba
      have h1 : @embed α _ N hN hChain I bij hI2 b <
                embed a :=
                @embed_order_strict α _ N hN hChain I bij hI2 b a hba
      rw [lt_iff_le_not_ge] at hba
      simp [himp, himp_Q]
      have h2 : a ⇨ b = b := @chain_himp _ _ hChain a b hba.right
      rw [h2]
      have hEmbed : ¬ (@embed α _ N hN hChain I bij hI2 a ≤ @embed α _ N hN hChain I bij hI2 b) := by
        rw [not_le]
        exact h1
      split_ifs
      · rfl
    · rename_i hba
      have hba := hba.symm
      have hab : a ≤ b := by simp [hba]
      have h1 : @embed α _ N hN hChain I bij hI2 a ≤
                embed b :=
                @embed_order α _ N hN hChain I bij hI2 a b hab
      have h2 : a ⇨ b = (⊤ : α) := by simp [hab]
      rw [h2]
      simp [himp, himp_Q]
      split_ifs
      · exact embed_top

lemma embed_inj {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  (@embed α _ N hN hChain I bij hI2).Injective := by
  intro a b hEmbed
  by_contra
  cases hChain a b
  · rename_i hab
    have hab : a < b := by
      rw [lt_iff_le_and_ne]
      exact And.intro hab this
    have hEmbed : @embed α _ N hN hChain I bij hI2 a <
                  embed b :=
                  @embed_order_strict α _ N hN hChain I bij hI2 a b hab
    rename_i temp _
    rw [lt_iff_le_and_ne] at hEmbed
    exact hEmbed.right temp
  · rename_i hab
    have this : ¬ b = a := by
      apply Ne.symm
      exact this
    have hab : b < a := by
      rw [lt_iff_le_and_ne]
      exact And.intro hab this
    have hEmbed : @embed α _ N hN hChain I bij hI2 b <
                  embed a :=
                  @embed_order_strict α _ N hN hChain I bij hI2 b a hab
    rename_i temp _ _
    rw [lt_iff_le_and_ne] at hEmbed
    have temp : @embed α _ N hN hChain I bij hI2 b =
                @embed α _ N hN hChain I bij hI2 a := temp.symm
    exact hEmbed.right temp

def Q_homomorphism (f : α → Q) : Prop := f Top.top = Top.top ∧
                f Bot.bot = Bot.bot ∧
                ∀ (a b : α),  (a ≤ b → f a ≤ f b) ∧
                f (a ⊓ b) = f a ⊓ f b ∧
                f (a ⊔ b) = f a ⊔ f b ∧
                f (a ⇨ b) = f a ⇨ f b

lemma embed_homo {hChain : chain α} {I : α → S N} {bij : I.Bijective}
  {hI2 : h01 I} :
  Q_homomorphism (@embed α _ N hN hChain I bij hI2) := by
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

noncomputable def lt_set [Fintype α] (a : α) : Finset α := {b : α | b < a}

noncomputable def normal_encoding [Fintype α] (a : α) : ℕ := Finset.card (lt_set a)

noncomputable def restricted_normal_encoding [Fintype α] (a : α) : Fin (Fintype.card α) :=
  ⟨normal_encoding a,
  by
    unfold normal_encoding
    apply Finset.card_lt_card
    rw [lt_set, Finset.filter_ssubset]
    exists ⊤
    simp
  ⟩

lemma restricted_normal_encoding_bij [Fintype α] {hChain : chain α} : (@restricted_normal_encoding α).Bijective := by
  rw [Nat.bijective_iff_injective_and_card]
  apply And.intro
  · intro a b
    unfold restricted_normal_encoding
    simp
    contrapose
    intro hab
    apply Or.elim (hChain a b)
    · intro hab'
      have hab : a < b := by
        rw [lt_iff_le_and_ne]
        exact And.intro hab' hab
      have ssub : lt_set a ⊂ lt_set b := by
        unfold lt_set
        rw [Finset.ssubset_def]
        apply And.intro
        · rw [Finset.subset_iff]
          intro x hx
          simp at *
          exact lt_trans hx hab
        · by_contra
          rw [Finset.subset_iff] at this
          have this := @this a
          have ha : a ∈ lt_set b := by
            simp [lt_set]
            exact hab
          have this := this ha
          simp at this
      have ssub : normal_encoding a < normal_encoding b := Finset.card_lt_card ssub
      have ssub : normal_encoding a ≠ normal_encoding b := by
        rw [ne_iff_gt_or_lt]
        exact Or.inr ssub
      exact ssub
    · intro hab'
      have hab : b ≠ a := by
        by_contra
        exact hab this.symm
      have hab : b < a := by
        rw [lt_iff_le_and_ne]
        exact And.intro hab' hab
      have ssub : lt_set b ⊂ lt_set a := by
        unfold lt_set
        rw [Finset.ssubset_def]
        apply And.intro
        · rw [Finset.subset_iff]
          intro x hx
          simp at *
          exact lt_trans hx hab
        · by_contra
          rw [Finset.subset_iff] at this
          have this := @this b
          have hb : b ∈ lt_set a := by
            simp [lt_set]
            exact hab
          have this := this hb
          simp at this
      have ssub : normal_encoding b < normal_encoding a := Finset.card_lt_card ssub
      have ssub : normal_encoding b ≠ normal_encoding a := by
        rw [ne_iff_gt_or_lt]
        exact Or.inr ssub
      by_contra
      exact ssub this.symm
  · simp

noncomputable def swapped_restricted_normal_encoding [Fintype α] : α → Fin (Fintype.card α) :=
  (Equiv.swap (restricted_normal_encoding Top.top) 1) ∘ restricted_normal_encoding

lemma swapped_restricted_normal_encoding_bij [Fintype α] {hChain : chain α} :
  (@swapped_restricted_normal_encoding α _ _).Bijective := by
  unfold swapped_restricted_normal_encoding
  apply Function.Bijective.comp
  simp
  exact @restricted_normal_encoding_bij α _ _ hChain

noncomputable def finite_encoding [Fintype α] (a : α) : S (Fintype.card α) :=
  ⟨swapped_restricted_normal_encoding a, by simp [mem_S]⟩

instance card_equiv [Fintype α] : S ((Fintype.card α)) ≃ Fin (Fintype.card α) := {
  toFun := (fun x => ⟨x, by
    obtain ⟨x, hx⟩ := x
    simp [S] at hx
    exact hx
  ⟩)
  invFun := (fun y => ⟨y, by
    simp [S]
  ⟩)
}

instance fin [Fintype α] : Finite (S (Fintype.card α)) := by
  rw [finite_iff_exists_equiv_fin]
  exists (Fintype.card α)
  apply Nonempty.intro
  exact card_equiv

noncomputable instance fintype [Fintype α] : Fintype (S (Fintype.card α)) :=
  @Fintype.ofFinite (S (Fintype.card α)) (@fin α _)

lemma finite_encoding_bij [Fintype α] {hChain : chain α} :
  (@finite_encoding α _ _).Bijective := by
  unfold finite_encoding
  rw [Nat.bijective_iff_injective_and_card]
  apply And.intro
  · intro a b hab
    simp at hab
    have hab : swapped_restricted_normal_encoding a = swapped_restricted_normal_encoding b := by
      rw [← Fin.val_inj]
      exact hab
    exact @(@swapped_restricted_normal_encoding_bij α _ _ hChain).left a b hab
  · have temp : Fintype.card (S ((Fintype.card α))) = Fintype.card (Fin (Fintype.card α)) := by
      rw [Fintype.card_eq]
      apply Nonempty.intro
      exact card_equiv
    simp [Nat.card_eq_fintype_card, temp]

lemma embedding {hN : Nontrivial α} {hC : Countable α} : chain α → ∃ (f : α → Q), Q_homomorphism f ∧ Function.Injective f := by
  intro h1
  by_cases hInf : Infinite α
  · have hD : Denumerable α := @Denumerable.ofEncodableOfInfinite α (@Encodable.ofCountable α hC) hInf
    let enum1 := hD.eqv
    let σ2 := Equiv.swap 1 (enum1 ⊤)
    let σ1 := Equiv.swap (σ2 0) (enum1 ⊥)
    let σ := σ1.trans σ2
    let id (n : ℕ) : S ⊤ := ⟨n, by simp [S]⟩
    let enum2 := id ∘ σ ∘ hD.eqv
    have h01 : enum2 Bot.bot = ⟨0, by simp [S]⟩ ∧
               enum2 Top.top = ⟨1, by simp [S]⟩ := by
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
    let f := @embed α _ ⊤ (by simp) h1 enum2 bij h01
    have Qhomof : Q_homomorphism f := embed_homo
    have Injf : Function.Injective f := embed_inj
    exists f
  · have hInf : Finite α := by
      rw [←not_infinite_iff_finite]
      exact hInf
    have hInf : Fintype α := Fintype.ofFinite α
    let enum := @finite_encoding α _ _
    have h1card : 1 < Fintype.card α := by
      rw [Fintype.one_lt_card_iff_nontrivial]
      exact hN
    have h0card : 0 < Fintype.card α := lt_trans zero_lt_one h1card
    have h01 :
      enum Bot.bot = ⟨0, by simp [S, h0card]⟩ ∧
      enum Top.top = ⟨1, by simp [S, h1card]⟩ := by
      apply And.intro
      · unfold enum
        unfold finite_encoding
        unfold swapped_restricted_normal_encoding
        simp
        rw [Equiv.swap_apply_def]
        split_ifs
        · exfalso
          rename_i h
          have temp : (⊥ : α) = (⊤ : α) := (@restricted_normal_encoding_bij α _ _ h1).left h
          exact bot_ne_top temp
        · exfalso
          rename_i h
          unfold restricted_normal_encoding at h
          unfold normal_encoding at h
          unfold lt_set at h
          simp at h
          simp [h] at h1card
        · unfold restricted_normal_encoding
          unfold normal_encoding
          unfold lt_set
          simp
      · unfold enum
        unfold finite_encoding
        unfold swapped_restricted_normal_encoding
        simp [Nat.one_mod_eq_one]
        have temp : Fintype.card α ≠ 1 := by
          by_contra
          simp [this] at h1card
        exact temp
    have bij : enum.Bijective := @finite_encoding_bij α _ _ h1
    let f := @embed α _ (Fintype.card α) (by simp [h1card]) h1 enum bij h01
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
    ¬true_in_alg_model (@filter_quot_var Γ F f.left.left) ϕ :=
    @chain_contradicting_valuation Γ ϕ notTrueInLTAlgebra
  obtain ⟨F, hF, hΓ', nhϕ'⟩ := h
  -- A/F is nontrivial (needed to construct the embedding)
  have hNontrivial : Nontrivial (Quotient (setoid_filter (hF := hF.left.left))) := by
    rw [nontrivial_iff]
    exists (AlgInterpretation filter_quot_var ϕ)
    exists ⊤
  -- take the embedding from A/F into Q
  have embed : ∃ (f : Quotient (setoid_filter (hF := hF.left.left)) → Q),
    Q_homomorphism f ∧ Function.Injective f := @embedding _ _ hNontrivial countable_quotient_algebra (quotient_chain hF)
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
