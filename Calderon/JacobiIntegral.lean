import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

open Set MeasureTheory
open scoped Topology

namespace OAI.AnisotropicCalderon.JacobiIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def leftMoment (f : ℝ → E) (t : ℝ) : E :=
  ∫ s in 0..t, s • f s

noncomputable def rightMoment (f : ℝ → E) (t : ℝ) : E :=
  ∫ s in t..1, (1-s) • f s

theorem leftMoment_eq (j j' f : ℝ → E) (t : ℝ) (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) :
    leftMoment f t = t • j' t - j t + j 0 := by
  have hs : Icc (0:ℝ) t ⊆ Icc 0 1 := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hF : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun u => u • j' u - j u) (s • f s) s := by
    intro s hs'
    have hsm := hs (by simpa [uIcc_of_le ht.1] using hs')
    convert! ((hasDerivAt_id s).smul (hj' s hsm)).sub (hj s hsm) using 1
    simp only [one_smul, id_eq]
    module
  have hint : IntervalIntegrable (fun s => s • f s) volume 0 t :=
    ((continuous_id.continuousOn.smul (hf.mono hs))).intervalIntegrable_of_Icc ht.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  simpa only [leftMoment, zero_smul, zero_sub, sub_neg_eq_add] using h

theorem rightMoment_eq (j j' f : ℝ → E) (t : ℝ) (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) :
    rightMoment f t = -(1-t) • j' t + j 1 - j t := by
  have hs : Icc t (1:ℝ) ⊆ Icc 0 1 := fun s hs => ⟨ht.1.trans hs.1,hs.2⟩
  have hF : ∀ s ∈ uIcc t 1,
      HasDerivAt (fun u => (1-u) • j' u + j u) ((1-s) • f s) s := by
    intro s hs'
    have hsm := hs (by simpa [uIcc_of_le ht.2] using hs')
    convert! (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).smul
      (hj' s hsm)).add (hj s hsm) using 1
    simp only [zero_sub, one_smul, Pi.sub_apply, id_eq, neg_smul]
    module
  have hc : ContinuousOn (fun s : ℝ => 1-s) (Icc t 1) :=
    (continuous_const.sub continuous_id).continuousOn
  have hint : IntervalIntegrable (fun s => (1-s) • f s) volume t 1 :=
    (hc.smul (hf.mono hs)).intervalIntegrable_of_Icc ht.2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  simp only [sub_self, zero_smul, zero_add] at h
  unfold rightMoment
  rw [h]
  module

theorem endpoint_representation (j j' f : ℝ → E) (t : ℝ) (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) :
    j t = (1-t) • j 0 + t • j 1 - (1-t) • leftMoment f t - t • rightMoment f t := by
  rw [leftMoment_eq j j' f t ht hj hj' hf, rightMoment_eq j j' f t ht hj hj' hf]
  module

theorem endpoint_derivative_representation (j j' f : ℝ → E) (t : ℝ)
    (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) :
    j' t - (j 1 - j 0) = leftMoment f t - rightMoment f t := by
  rw [leftMoment_eq j j' f t ht hj hj' hf, rightMoment_eq j j' f t ht hj hj' hf]
  module

#print axioms endpoint_representation
#print axioms endpoint_derivative_representation
end OAI.AnisotropicCalderon.JacobiIntegral
