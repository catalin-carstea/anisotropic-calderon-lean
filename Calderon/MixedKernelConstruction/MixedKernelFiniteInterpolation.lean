import Calderon.MixedKernelConstruction.MixedKernelObservedOutputRooms
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Filter Metric MeasureTheory
open scoped Topology

/-- Lowering a positive interpolation exponent weakens the estimate when the observed
norm is at most the full norm. Zero data are included. -/
theorem interpolation_weight_antitone {S D a b : ℝ}
    (hS : 0 ≤ S) (hSD : S ≤ D) (ha : 0 < a) (hab : a ≤ b) :
    S^b*D^(1-b) ≤ S^a*D^(1-a) := by
  have hD : 0 ≤ D := hS.trans hSD
  have hb : 0 < b := ha.trans_le hab
  by_cases hDz : D = 0
  · have hSz : S = 0 := le_antisymm (hSD.trans_eq hDz) hS
    rw [hSz,hDz,Real.zero_rpow hb.ne',Real.zero_rpow ha.ne',zero_mul,zero_mul]
  have hDp : 0 < D := hD.lt_of_ne' hDz
  by_cases hSz : S = 0
  · rw [hSz,Real.zero_rpow hb.ne',Real.zero_rpow ha.ne',zero_mul,zero_mul]
  have hSp : 0 < S := hS.lt_of_ne' hSz
  have hr : 0 < S/D := div_pos hSp hDp
  have hr1 : S/D ≤ 1 := (div_le_one hDp).2 hSD
  have hm := Real.rpow_le_rpow_of_exponent_ge hr hr1 hab
  have heq (t : ℝ) : S^t*D^(1-t) = D*(S/D)^t := by
    rw [Real.div_rpow hS hD,Real.rpow_sub hDp,Real.rpow_one]
    ring
  rw [heq b,heq a]
  exact mul_le_mul_of_nonneg_left hm hD

/-- A finite cover combines actual squared L2 estimates with one positive exponent.
The output coefficient and exponent are independent of the particular square-integrable q. -/
theorem finite_cover_interpolation_sq {ι : Type*} (s : Finset ι)
    (E : ι → Set R3) (K Dset : Set R3) (hK : MeasurableSet K)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) (hED : ∀ i ∈ s, E i ⊆ Dset)
    (hcover : K ⊆ ⋃ i ∈ s, E i) (q : R3 → ℝ)
    (hq : IntegrableOn (fun x => q x^2) Dset)
    (S D a : ℝ) (C gamma : ι → ℝ)
    (hS : 0 ≤ S) (hSD : S ≤ D) (ha : 0 < a)
    (hC : ∀ i ∈ s, 0 ≤ C i) (hgamma : ∀ i ∈ s, a ≤ gamma i)
    (hbound : ∀ i ∈ s, (∫ x in E i, q x^2) ≤ (C i*(S^(gamma i)*D^(1-gamma i)))^2) :
    (∫ x in K, q x^2) ≤ (∑ i ∈ s, (C i)^2)*(S^a*D^(1-a))^2 := by
  classical
  have hKD : K ⊆ Dset := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact hED i hi hxi
  have hIK : Integrable (K.indicator (fun x => q x^2)) :=
    (integrable_indicator_iff hK).2 (hq.mono_set hKD)
  have hIE : ∀ i ∈ s, Integrable ((E i).indicator (fun x => q x^2)) :=
    fun i hi => (integrable_indicator_iff (hE i hi)).2 (hq.mono_set (hED i hi))
  have hsum : Integrable (fun x => ∑ i ∈ s, (E i).indicator (fun y => q y^2) x) :=
    integrable_finsetSum s hIE
  have hpt : ∀ x, K.indicator (fun y => q y^2) x ≤
      ∑ i ∈ s, (E i).indicator (fun y => q y^2) x := by
    intro x
    have hnonneg : ∀ i, 0 ≤ (E i).indicator (fun y => q y^2) x :=
      fun i => indicator_nonneg (fun y _ => sq_nonneg (q y)) x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
      calc q x^2 = (E i).indicator (fun y => q y^2) x := by rw [indicator_of_mem hxi]
        _ ≤ ∑ j ∈ s, (E j).indicator (fun y => q y^2) x :=
          Finset.single_le_sum (fun j _ => hnonneg j) hi
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i _ => hnonneg i)
  have hcoverInt : (∫ x in K, q x^2) ≤ ∑ i ∈ s, ∫ x in E i, q x^2 := by
    have hmono := integral_mono hIK hsum hpt
    rw [integral_indicator hK,integral_finsetSum s hIE] at hmono
    have heq : (∑ i ∈ s, ∫ x, (E i).indicator (fun y => q y^2) x) =
        ∑ i ∈ s, ∫ x in E i, q x^2 :=
      Finset.sum_congr rfl (fun i hi => integral_indicator (hE i hi))
    exact hmono.trans_eq heq
  apply hcoverInt.trans
  calc
    (∑ i ∈ s, ∫ x in E i, q x^2) ≤ (∑ i ∈ s, (C i)^2*(S^a*D^(1-a))^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hm := interpolation_weight_antitone hS hSD ha (hgamma i hi)
      have hwi : 0 ≤ S^(gamma i)*D^(1-gamma i) :=
        mul_nonneg (Real.rpow_nonneg hS _) (Real.rpow_nonneg (hS.trans hSD) _)
      have hsq := pow_le_pow_left₀ (mul_nonneg (hC i hi) hwi)
        (mul_le_mul_of_nonneg_left hm (hC i hi)) 2
      exact (hbound i hi).trans (hsq.trans_eq (by ring))
    _ = (∑ i ∈ s, (C i)^2)*(S^a*D^(1-a))^2 := (Finset.sum_mul _ _ _).symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
