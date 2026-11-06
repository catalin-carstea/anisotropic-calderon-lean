import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreSpace

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def finiteHarmonicBlockCutoff (n : ℕ)
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) :
    SphereL2 →L[ℝ] SphereL2 :=
  ∑ k ∈ Finset.range n, (harmonicSphereSubspace k).subtypeL.comp
    ((K k).comp (sphereHarmonicCoordinate hO hD k))

lemma sphereHarmonicCoordinate_subtype_of_ne (k l : ℕ) (hkl : k ≠ l)
    (u : harmonicSphereSubspace l) :
    sphereHarmonicCoordinate hO hD k (u : SphereL2) = 0 := by
  rw [sphereHarmonicCoordinate_apply, sphereHarmonicDecomposition_subtype]
  simp [lp.single_apply, hkl]

lemma finiteHarmonicBlockCutoff_coordinate (n : ℕ)
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)
    (u : SphereL2) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (finiteHarmonicBlockCutoff hO hD n K u) =
      if k < n then K k (sphereHarmonicCoordinate hO hD k u) else 0 := by
  classical
  simp only [finiteHarmonicBlockCutoff, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, map_sum]
  by_cases hk : k < n
  · rw [if_pos hk, Finset.sum_eq_single k]
    · exact sphereHarmonicCoordinate_subtype hO hD k _
    · intro l hl hlk
      exact sphereHarmonicCoordinate_subtype_of_ne hO hD k l (Ne.symm hlk) _
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hk)).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro l hl
    have hkl : k ≠ l := by
      intro h
      subst l
      exact hk (Finset.mem_range.mp hl)
    exact sphereHarmonicCoordinate_subtype_of_ne hO hD k l hkl _

lemma finiteHarmonicBlockCutoff_coordinate_of_band (n : ℕ)
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)
    (F : R3 → SphereL2) (hF : finiteHarmonicBand hO hD n F) (x : R3) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (finiteHarmonicBlockCutoff hO hD n K (F x)) =
      K k (sphereHarmonicCoordinate hO hD k (F x)) := by
  rw [finiteHarmonicBlockCutoff_coordinate]
  by_cases hk : k < n
  · rw [if_pos hk]
  · rw [if_neg hk, hF x k (Nat.le_of_not_gt hk), map_zero]


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
