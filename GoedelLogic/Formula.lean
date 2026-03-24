-- Primarily Trufas' work, with some changes to the proofs to fit my style

import Mathlib.Data.Countable.Basic

set_option autoImplicit false

structure Var where
  val : Nat

-- Inductive definition of propositional formulae
inductive Formula where
| var : Var → Formula
| bottom : Formula
| and : Formula → Formula → Formula
| or : Formula → Formula → Formula
| implication : Formula → Formula → Formula

namespace Formula

notation "⊥" => bottom

infixl:60 " ∧∧ " => and

infixl:60 " ∨∨ " => or

infixr:50 (priority := high) " ⇒ " => implication

def equivalence (ϕ ψ : Formula) := (ϕ ⇒ ψ) ∧∧ (ψ ⇒ ϕ)
infix:40 " ⇔ " => equivalence

def negation (ϕ : Formula) : Formula := ϕ ⇒ ⊥
prefix:70 " ~ " => negation

def top : Formula := ~⊥
notation " ⊤ " => top

def pairing (x y : ℕ) := (x + y) * (x + y + 1) + 2 * x

-- Shortened proof of pairing_0
lemma pairing_0 {x y : ℕ} : pairing x y = 0 → x = 0 ∧ y = 0 :=
  by
    intro h
    simp [pairing, Nat.mul_eq_zero] at h
    exact h.left
/-
lemma pairing_inj1 (x y z t : ℕ) : pairing x y = pairing z t ↔ x = z ∧ y = t := by
  apply Iff.intro
  · intro h
    set a := x + y with ha
    set b := z + t with hb
    simp only [pairing, ←ha,←hb] at h
    by_cases hab : a = b
    · rw [hab] at h
      have hxz : x = z := by
        rw [Nat.add_left_cancel_iff, Nat.mul_left_cancel_iff] at h
        exact h
        apply Nat.zero_lt_succ
      have hyt : y = t := by
        rw [ha, hb, hxz, Nat.add_left_cancel_iff] at hab
        exact hab
      exact And.intro hxz hyt
    · exfalso
      by_cases hab : a < b
      · set d := b - a with hd
        have hd' : b = d + a := by
          apply Nat.eq_add_of_sub_eq
          · apply Nat.le_of_lt hab
          · rfl
        rw [hd'] at h
        --have hle
        have h : a*(a + 1) + 2*x - 2*z = (d + a)*(d + a + 1) := by
          apply Nat.sub_eq_of_eq_add at h
          exact h
        have h : 2*x - 2*z = (d + a)*(d + a + 1) - a*(a + 1) := by
          simp [h]
-/


-- TODO: attempt to shorten proof of pairing_inj?
lemma pairing_inj (x y z t : ℕ) : pairing x y = pairing z t ↔
  x = z ∧ y = t :=
  by
    apply Iff.intro
    · intro Heq
      unfold pairing at Heq
      let a := x + y
      let b := z + t
      have Heq' : a * (a + 1) + 2 * x = b * (b + 1) + 2 * z := by assumption
      by_cases h : a = b
      · rw [h] at Heq'
        simp at Heq'
        let Hxz : x = z :=
          by
            apply @Nat.eq_of_mul_eq_mul_left x z 2
            · simp
            · assumption
        apply And.intro
        · assumption
        · simp [a, b] at h
          rw [Hxz] at h
          simp at h
          assumption
      · exfalso
        by_cases Hab : a < b
        · let d := b - a
          have Haux : b = d + a :=
            by
              apply Nat.eq_add_of_sub_eq
              · apply Nat.le_of_lt Hab
              · rfl
          rw [Haux] at Heq'
          have Heq'' : 2 * x = (d + a) * (d + a + 1) + 2 * z - a * (a + 1) :=
            by
              symm
              apply Nat.sub_eq_of_eq_add
              symm
              rw [Nat.add_comm]
              assumption
          have Heq'' : 2 * x - 2 * z = (d + a) * (d + a + 1) - a * (a + 1) :=
            by
              apply Nat.sub_eq_of_eq_add
              have Haux' : ∀ (a b c : ℕ), c ≤ a → a + b - c = a - c + b :=
                by
                  intro a b c Hle
                  apply Nat.sub_eq_of_eq_add
                  symm
                  rw [Nat.add_comm, <-Nat.add_assoc]
                  simp
                  apply Nat.add_sub_of_le Hle
              have Hle : a * (a + 1) ≤ (d + a) * (d + a + 1) :=
                by
                  apply Nat.mul_le_mul
                  · simp
                  · simp
              let Haux'' := Haux' ((d + a) * (d + a + 1)) (2 * z) (a * (a + 1)) Hle
              rw [<-Haux'']
              assumption
          rw [<-Nat.mul_sub_left_distrib] at Heq''
          rw [Nat.mul_add, Nat.mul_add, Nat.right_distrib, Nat.mul_one] at Heq''
          have Haux : (d + a) * a = d * a + a * a := by rw [Nat.add_mul]
          rw [Haux] at Heq''
          have Haux : a * (a + 1) = a * a + a := by rw [Nat.mul_add, Nat.mul_one]
          rw [Haux, <-Nat.sub_sub] at Heq''
          rw [<-Nat.add_assoc] at Heq''
          have Haux : d * d + a * d + (d * a + a * a) = d * d + a * d + d * a + a * a :=
            by rw [<-Nat.add_assoc]
          rw [Haux] at Heq''
          rw [<-Nat.sub_add_eq, Nat.add_sub_add_right, Nat.add_assoc, Nat.add_sub_assoc, Nat.add_sub_cancel_left] at Heq''
          · have Hge : 2 * (x - z) ≥ 2 * (a + 1) :=
              by
                rw [Heq'']
                have Haux : 2 * (a + 1) = 2 + 2 * a := by rw [Nat.mul_add, Nat.add_comm]
                rw [Haux]
                rw [Nat.add_comm, <-Nat.add_assoc, <-Nat.add_assoc, Nat.add_assoc]
                have Hd : d >= 1 := by apply Nat.sub_pos_of_lt Hab
                apply Nat.add_le_add
                · have Hd2 : d * d >= 1 := by rw [<-Nat.mul_one 1]; apply Nat.mul_le_mul; assumption'
                  apply Nat.add_le_add Hd Hd2
                · rw [Nat.succ_mul]
                  apply Nat.add_le_add
                  · rw [Nat.mul_comm]
                    apply Nat.mul_le_mul
                    · rfl
                    · assumption
                  · rw [<-Nat.one_mul a]
                    apply Nat.mul_le_mul
                    · assumption
                    · rw [Nat.one_mul]
            have Hge : x - z ≥ a + 1 := by apply Nat.le_of_mul_le_mul_left Hge; simp
            have Hge := Nat.add_lt_of_lt_sub (Nat.lt_of_succ_le Hge)
            rw [Nat.add_assoc] at Hge
            let Haux := Nat.le_add_right x (y + z)
            let Hge := Nat.not_le_of_lt Hge
            contradiction
          · simp only [Nat.le_add_right]
        · let d := a - b
          have Haux : a = d + b :=
            by
              apply Nat.eq_add_of_sub_eq
              · rw [Nat.not_lt_eq] at Hab; assumption
              · rfl
          rw [Haux] at Heq'
          have Heq'' : 2 * z = (d + b) * (d + b + 1) + 2 * x - b * (b + 1) :=
            by
              symm
              apply Nat.sub_eq_of_eq_add
              symm
              rw [Nat.add_comm]
              symm
              assumption
          have Heq'' : 2 * z - 2 * x = (d + b) * (d + b + 1) - b * (b + 1) :=
            by
              apply Nat.sub_eq_of_eq_add
              have Haux' : ∀ (a b c : ℕ), c ≤ a → a + b - c = a - c + b :=
                by
                  intro a b c Hle
                  apply Nat.sub_eq_of_eq_add
                  symm
                  rw [Nat.add_comm, <-Nat.add_assoc]
                  simp
                  apply Nat.add_sub_of_le Hle
              have Hle : b * (b + 1) ≤ (d + b) * (d + b + 1) :=
                by
                  apply Nat.mul_le_mul
                  · simp
                  · simp
              let Haux'' := Haux' ((d + b) * (d + b + 1)) (2 * x) (b * (b + 1)) Hle
              rw [<-Haux'']
              assumption
          rw [<-Nat.mul_sub_left_distrib] at Heq''
          rw [Nat.mul_add, Nat.mul_add, Nat.right_distrib, Nat.mul_one] at Heq''
          have Haux : (d + b) * b = d * b + b * b := by rw [Nat.add_mul]
          rw [Haux] at Heq''
          have Haux : b * (b + 1) = b * b + b := by rw [Nat.mul_add, Nat.mul_one]
          rw [Haux, <-Nat.sub_sub] at Heq''
          rw [<-Nat.add_assoc] at Heq''
          have Haux : d * d + b * d + (d * b + b * b) = d * d + b * d + d * b + b * b :=
            by rw [<-Nat.add_assoc]
          rw [Haux] at Heq''
          rw [<-Nat.sub_add_eq, Nat.add_sub_add_right, Nat.add_assoc, Nat.add_sub_assoc, Nat.add_sub_cancel_left] at Heq''
          · have Hge : 2 * (z - x) ≥ 2 * (b + 1) :=
              by
                rw [Heq'']
                have Haux : 2 * (b + 1) = 2 + 2 * b := by rw [Nat.mul_add, Nat.add_comm]
                rw [Haux]
                rw [Nat.add_comm, <-Nat.add_assoc, <-Nat.add_assoc, Nat.add_assoc]
                let Ht := Nat.lt_trichotomy a b
                rcases Ht with Hl | Heg
                · contradiction
                · rcases Heg with He | Hg
                  · contradiction
                  · have Hd : d >= 1 := by apply Nat.sub_pos_of_lt Hg
                    apply Nat.add_le_add
                    · have Hd2 : d * d >= 1 := by rw [<-Nat.mul_one 1]; apply Nat.mul_le_mul; assumption'
                      apply Nat.add_le_add Hd Hd2
                    · rw [Nat.succ_mul]
                      apply Nat.add_le_add
                      · rw [Nat.mul_comm]
                        apply Nat.mul_le_mul
                        · rfl
                        · assumption
                      · rw [<-Nat.one_mul b]
                        apply Nat.mul_le_mul
                        · assumption
                        · rw [Nat.one_mul]
            have Hge : z - x ≥ b + 1 := by apply Nat.le_of_mul_le_mul_left Hge; simp
            have Hge := Nat.add_lt_of_lt_sub (Nat.lt_of_succ_le Hge)
            simp at Hge
            rw [Nat.add_assoc] at Hge
            let Haux := Nat.le_add_right z (t + x)
            let Hge := Nat.not_le_of_lt Hge
            contradiction
          · simp
    · intro Heq
      rw [Heq.left, Heq.right]

def encode_form : Formula → ℕ
  | var v => pairing 0 (v.val + 1)
  | bottom => 0
  | ϕ ∧∧ ψ => pairing (pairing (encode_form ϕ) 1) (encode_form ψ)
  | ϕ ∨∨ ψ => pairing (pairing (encode_form ϕ) 2) (encode_form ψ)
  | ϕ ⇒ ψ => pairing (pairing (encode_form ϕ) 3) (encode_form ψ)

theorem inject_Form : encode_form.Injective :=
  by
    intro ϕ ψ h
    induction ϕ generalizing ψ with
    | var v1 => cases ψ
                · simp only [encode_form, var.injEq] at *
                  rw [pairing_inj] at h;
                  rcases h with ⟨_, hr⟩
                  simp only [Nat.add_right_cancel_iff] at hr
                  exact congrArg Var.mk hr
                · simp [encode_form] at *; let h := pairing_0 h
                  rcases h
                  contradiction
                repeat { simp only [encode_form, reduceCtorEq] at *
                         rw [pairing_inj] at h;
                         rcases h with ⟨hl, hr⟩
                         symm at hl
                         let hl := pairing_0 hl
                         rcases hl
                         contradiction }
    | bottom => cases ψ
                · simp only [encode_form, reduceCtorEq] at *
                  symm at h
                  let h := pairing_0 h
                  rcases h with ⟨_, hr⟩
                  simp only [Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false] at hr
                · simp only [encode_form] at *
                repeat { simp only [encode_form, reduceCtorEq] at *
                         symm at h
                         let h := pairing_0 h
                         let hl := pairing_0 h.left
                         rcases hl
                         contradiction }
    | and a b ih1 ih2 | or a b ih1 ih2 | implication a b ih1 ih2 => cases ψ <;> simp [encode_form] at *
                                                                    · rw [pairing_inj] at h
                                                                      let hl := pairing_0 h.left
                                                                      rcases hl
                                                                      contradiction
                                                                    · let h := pairing_0 h
                                                                      let hl := pairing_0 h.left
                                                                      rcases hl
                                                                      contradiction
                                                                    repeat { rw [pairing_inj] at h
                                                                             rcases h with ⟨hl, hr⟩
                                                                             rw [pairing_inj] at hl
                                                                             first | exact And.intro (ih1 hl.left) (ih2 hr) | rcases hl; contradiction }

-- Would use this if I were to prove that A/F is countable
instance : Countable Formula := inject_Form.countable

instance : Nonempty Formula := ⟨⊥⟩
