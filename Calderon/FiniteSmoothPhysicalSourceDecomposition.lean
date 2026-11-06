import Calderon.ActualPhysicalDensityOperatorGermCongruence
import Mathlib.Geometry.Manifold.PartitionOfUnity
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Manifold
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore

theorem exists_smooth_finite_weights_subordinate_to_compact_cover
    (n:ℕ) (K:Set R3) (hK:IsCompact K) (U:Fin n→Set R3) (hU:∀ i,IsOpen (U i))
    (hCover:∀ y∈K,∃ i,y∈U i):
    ∃ theta:Fin n→R3→ℝ,(∀ i,ContDiff ℝ ∞ (theta i)) ∧
      (∀ i,tsupport (theta i)⊆U i) ∧ (∀ y∈K,∑ i,theta i y=1) ∧
      (∀ i y,theta i y∈Icc (0:ℝ) 1) := by
  classical
  obtain ⟨rho,hRho⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I:=𝓘(ℝ,R3)) hK.isClosed U hU
    (by intro y hy;exact mem_iUnion.mpr (hCover y hy))
  refine ⟨fun i y => rho i y,?_,hRho,?_,?_⟩
  · intro i
    simpa only [contMDiff_iff_contDiff] using (rho i).contMDiff
  · intro y hy
    simpa only [finsum_eq_sum_of_fintype] using rho.sum_eq_one hy
  · intro i y
    exact ⟨rho.nonneg i y,rho.le_one i y⟩

theorem exists_exact_smooth_finite_source_decomposition
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n:ℕ) (u:R3→E) (hu:ContDiff ℝ ∞ u) (hc:HasCompactSupport u)
    (U:Fin n→Set R3) (hU:∀ i,IsOpen (U i)) (hCover:∀ y∈tsupport u,∃ i,y∈U i):
    ∃ v:Fin n→R3→E,(∀ i,ContDiff ℝ ∞ (v i) ∧ HasCompactSupport (v i) ∧
      tsupport (v i)⊆tsupport u∩U i) ∧ (∀ y:R3,∑ i,v i y=u y) := by
  classical
  obtain ⟨theta,hTheta,hSupp,hSum,hRange⟩ :=
    exists_smooth_finite_weights_subordinate_to_compact_cover n (tsupport u) hc U hU hCover
  let v:Fin n→R3→E := fun i y => theta i y • u y
  refine ⟨v,?_,?_⟩
  · intro i
    refine ⟨(hTheta i).smul hu,hc.smul_left,?_⟩
    intro y hy
    exact ⟨tsupport_smul_subset_right _ _ hy,hSupp i (tsupport_smul_subset_left _ _ hy)⟩
  · intro y
    by_cases hy:y∈tsupport u
    · change (∑ i,theta i y • u y)=u y
      rw [← Finset.sum_smul,hSum y hy,one_smul]
    · have hz:u y=0 := image_eq_zero_of_notMem_tsupport hy
      simp only [v,hz,smul_zero,Finset.sum_const_zero]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
