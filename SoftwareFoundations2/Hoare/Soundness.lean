import SoftwareFoundations2.Hoare.Logic

open AExp
open BExp

namespace Hoare

lemma hoare_skip : ⊨ ⦃ P ⦄ ⟨{ skip }⟩ ⦃ P ⦄ := by
  unfold Valid
  intros σ σ' h hp
  cases h
  exact hp

lemma hoare_asgn : ⊨ ⦃ P[a // x] ⦄ ⟨{ ↑x = ↑a }⟩ ⦃ P ⦄ := by
  unfold Valid
  intros σ σ' h hp
  cases h with
  | EAsgn h1 h2 =>
    rw [h1] at h2
    unfold Assertion.subst at hp
    rw [← h2] at hp
    exact hp

lemma hoare_seq
    (h₁ : ⊨ ⦃ P ⦄ c₁ ⦃ Q ⦄)
    (h₂ : ⊨ ⦃ Q ⦄ c₂ ⦃ R ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ ↑c₁ ; ↑c₂}⟩ ⦃ R ⦄ := by
  unfold Valid
  intros σ σ' h hp
  cases h with
  | @ESeq _ _ σ'' _ _ h1 h2 =>
    unfold Valid at h₁
    unfold Valid at h₂
    specialize h₁ σ σ''
    specialize h₂ σ'' σ'
    have hq := h₁ h1 hp
    have hr := h₂ h2 hq
    exact hr

lemma hoare_if {b : BExp}
      (h₁ : ⊨ ⦃ P ∧ b ⦄ c₁ ⦃ Q ⦄)
      (h₂ : ⊨ ⦃ P ∧ ¬b ⦄ c₂ ⦃ Q ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ⦃ Q ⦄ := by
  unfold Valid
  intros σ σ' h hp
  cases h with
  | EIfTrue hb hc =>
    unfold Valid at h₁
    specialize h₁ σ σ'
    unfold Assertion.and at h₁
    simp only [assert, and_imp] at h₁
    exact h₁ hc hp hb
  | EIfFalse hf hc =>
    unfold Valid at h₂
    specialize h₂ σ σ'
    unfold Assertion.and at h₂
    simp only [Assertion.neg, assert, Bool.not_eq_true, and_imp] at h₂
    exact h₂ hc hp hf


lemma hoare_while {b : BExp}
      (h : ⊨ ⦃ P ∧ b ⦄ c ⦃ P ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ while ↑b do ↑c od }⟩ ⦃ P ∧ ¬b ⦄ := by
  unfold Valid
  intros σ σ'
  generalize eq : ⟨{ while ↑b do ↑c od }⟩ = loop
  intros h1 hp
  induction h1 with
  | @EWhileTrue  σ₁ _ σ₂ _ σ₃ htrue h1 h2 h3 h4 =>
    have h5 := h4 eq
    simp_all only [Assertion.and, Assertion.neg, assert, Bool.not_eq_true, forall_const,
      not_false_eq_true, and_self, implies_true, Com.CWhile.injEq, true_and]
    obtain ⟨left, right⟩ := eq
    subst left right
    unfold Valid at h
    specialize h σ₁ σ₂
    simp only [Assertion.and, assert, and_imp] at h
    have hp1 := h h1 hp htrue
    exact h5 hp1
  | EWhileFalse hfalse => aesop
  | _ => aesop

lemma hoare_consequence
    (hPre : P ->> P')
    (hPost : Q' ->> Q)
    (hH : ⊨ ⦃ P' ⦄ c ⦃ Q' ⦄) :
  ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  unfold Valid
  intros σ σ' hc hp
  unfold Valid at hH
  specialize hH σ σ'
  -- simp_all only [Assertion.implies, Assertion.true, Assertion.impl, forall_const]
  simp only [Assertion.implies, Assertion.true, Assertion.impl] at hPre
  specialize hPre σ
  simp only [Assertion.implies, Assertion.true, Assertion.impl] at hPost
  specialize hPost σ'
  have hp' := hPre hp
  have hq':= hH hc hp'
  exact hPost hq'

def Soundness :
  ⊢ ⦃ P ⦄ c ⦃ Q ⦄ → ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  intro h
  induction h with
  | HSkip =>
      exact hoare_skip
  | HAsgn =>
      exact hoare_asgn
  | @HSeq P c₁ Q c₂ R _ _ ih₁ ih₂ =>
      apply hoare_seq
      repeat assumption
  | HIf _ _ ih₁ ih₂ =>
      apply hoare_if ih₁ ih₂
  | @HWhile P c b _ ih =>
      apply hoare_while ih
  | HConsequence h₁ h₂ _ ih =>
      apply hoare_consequence
      repeat assumption

end Hoare
