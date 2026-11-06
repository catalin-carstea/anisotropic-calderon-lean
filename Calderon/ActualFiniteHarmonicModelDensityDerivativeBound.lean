import Calderon.ActualMixedDensityHigherCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open ReferenceDensityBounds PrincipalCommutator ActualMixedDensityHigherCoefficientJets
  ActualReferenceDDHigherGeometryJets

theorem exists_referenceDensity_uniform_relative_coordinate_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ i : Fin 3,
      |directionalFDeriv (coordinateDirection i)
        (fun y => referenceDensityFamily g L (lam,y)) x| ≤
        C*referenceDensityFamily g L (lam,x) := by
  obtain ⟨M,hM,hbound⟩ := exists_mixed_background_coordinate_jet_bound g hg L K hK 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨M^2,sq_pos_of_pos hMpos,?_⟩
  intro lam hlam x hx i
  let mu := referenceDensityFamily g L (lam,x)
  have hmu : 0 < mu := referenceDensityFamily_pos g hg L (lam,x)
  have hInv : mu⁻¹ ≤ M := by
    simpa only [coordinateFieldWordPartial,abs_of_pos (inv_pos.mpr hmu),mu] using
      (hbound lam hlam x hx).2.2.2 [] (by simp)
  have hOne : 1 ≤ mu*M := by
    have ht := mul_le_mul_of_nonneg_left hInv hmu.le
    simpa only [mul_inv_cancel₀ hmu.ne'] using ht
  have hd : |directionalFDeriv (coordinateDirection i)
      (fun y => referenceDensityFamily g L (lam,y)) x| ≤ M := by
    simpa only [coordinateFieldWordPartial] using
      (hbound lam hlam x hx).2.2.1 [i] (by simp)
  calc
    _ ≤ M := hd
    _ ≤ M^2*mu := by nlinarith [mul_le_mul_of_nonneg_left hOne hMpos.le]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
