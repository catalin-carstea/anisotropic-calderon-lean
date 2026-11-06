import Calderon.SphereSobolevFinitePhysicalHalfDualPackets
import Calderon.SphereSobolevFiniteHalfDualDenseExtension
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
/-! Abstract pointwise step in the actual space; the inverse-family graph and the
finite bound are derived separately. -/
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevInclusionL

lemma sphereSobolev_finite_half_dual_degree_form_of_coefficients
    (T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (K : ∀ m n : ℕ, harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (hCoefficients : ∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (T (sphereSobolevSingleL (3/2:ℝ) n z)) = ((m:ℝ)-(n:ℝ)) • K m n z)
    (ncut : ℕ) (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev (1/2:ℝ))
    (hu : ∀ k, ncut ≤ k → sphereSobolevCoefficientL (3/2:ℝ) k u = 0)
    (hv : ∀ k, ncut ≤ k → sphereSobolevCoefficientL (1/2:ℝ) k v = 0) :
    sphereSobolevDualPairing (1/2:ℝ) v (T u) =
      ∑ m ∈ Finset.range ncut, ∑ n ∈ Finset.range ncut,
        ((m:ℝ)-(n:ℝ))*⟪K m n (sphereSobolevCoefficientL (3/2:ℝ) n u),sphereSobolevCoefficientL (1/2:ℝ) m v⟫_ℝ := by
  have hU := sphereSobolev_eq_physical_packet_of_finiteSupport (3/2:ℝ) ncut u hu
  have hV := sphereSobolev_eq_physical_packet_of_finiteSupport (1/2:ℝ) ncut v hv
  have hInput (m : ℕ) : sphereSobolevCoefficientL (-(1/2:ℝ)) m (T u) =
      ∑ n ∈ Finset.range ncut, ((m:ℝ)-(n:ℝ)) • K m n (sphereSobolevCoefficientL (3/2:ℝ) n u) := by
    have hMapped := (congrArg T hU).trans
      (map_sum T (fun n => sphereSobolevSingleL (3/2:ℝ) n (sphereSobolevCoefficientL (3/2:ℝ) n u)) (Finset.range ncut))
    have hCoeff := (congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m) hMapped).trans
      (map_sum (sphereSobolevCoefficientL (-(1/2:ℝ)) m)
        (fun n => T (sphereSobolevSingleL (3/2:ℝ) n (sphereSobolevCoefficientL (3/2:ℝ) n u))) (Finset.range ncut))
    exact hCoeff.trans (Finset.sum_congr rfl (fun n _ => hCoefficients m n (sphereSobolevCoefficientL (3/2:ℝ) n u)))
  have hPair := (congrArg (fun wv : SphereSobolev (1/2:ℝ) => sphereSobolevDualPairing (1/2:ℝ) wv (T u)) hV).trans
    (sphereSobolevDualPairing_finite_left_physical (1/2:ℝ) (Finset.range ncut)
      (fun m => sphereSobolevCoefficientL (1/2:ℝ) m v) (T u))
  refine hPair.trans ?_
  apply Finset.sum_congr rfl
  intro m _
  rw [hInput,sum_inner]
  apply Finset.sum_congr rfl
  intro n _
  exact real_inner_smul_left (K m n (sphereSobolevCoefficientL (3/2:ℝ) n u))
    (sphereSobolevCoefficientL (1/2:ℝ) m v) ((m:ℝ)-(n:ℝ))

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_finite_half_dual_degree_form_of_coefficients
end OAI.AnisotropicCalderon.SphereHarmonic
