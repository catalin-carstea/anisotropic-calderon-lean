import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.NativeFirstCorrectionBandGraphs
import Calderon.ActualFirstCorrectionSobolevFamilies
import Calderon.ActualReferenceSharpMidpointRadialCoefficients
import Mathlib.Tactic.Module

/-! Native bands with degree zero retained, the genuine pivot transpose, and the same
lower DN map. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ENNReal InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily DirichletFamily.DriftBootstrap
attribute [local irreducible] sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL sphereSobolevShiftedDegreeL

lemma sphereSobolevLinearCoordinateMul_degree_commutator_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevLinearCoordinateMulL hF hO hD (s-1) d
      (sphereSobolevShiftedDegreeL s (sphereSobolevSingleL s k a)) -
    sphereSobolevShiftedDegreeL s
      (sphereSobolevLinearCoordinateMulL hF hO hD s d (sphereSobolevSingleL s k a)) =
    sphereSobolevInclusionL s (s-1) (by linarith)
      (sphereSobolevRadialDriftAdjointL hF hO hD s d (sphereSobolevSingleL s k a) -
       sphereSobolevRadialDriftL hF hO hD s d (sphereSobolevSingleL s k a)) := by
  cases k with
  | zero => exact linearCoordinate_degree_commutator_constant_graph hF hO hD s d a
  | succ k => exact linearCoordinate_degree_commutator_succ_graph hF hO hD s d k a

lemma sphereSobolevLinearCoordinateMul_degree_commutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) :
    (sphereSobolevLinearCoordinateMulL hF hO hD (s-1) d).comp (sphereSobolevShiftedDegreeL s) -
      (sphereSobolevShiftedDegreeL s).comp (sphereSobolevLinearCoordinateMulL hF hO hD s d) =
    (sphereSobolevInclusionL s (s-1) (by linarith)).comp
      (sphereSobolevRadialDriftAdjointL hF hO hD s d - sphereSobolevRadialDriftL hF hO hD s d) := by
  apply sphereSobolev_clm_eq_of_single s
  intro k a
  exact sphereSobolevLinearCoordinateMul_degree_commutator_single hF hO hD s d k a

lemma sphereSobolevLinearCoordinateMul_half_degree_commutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (u : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) u) -
    sphereSobolevShiftedDegreeL (1/2 : ℝ)
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d u) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d u -
       sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d u) := by
  have h := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev ((1/2 : ℝ)-1) => A u)
      (sphereSobolevLinearCoordinateMul_degree_commutator hF hO hD (1/2 : ℝ) d)
  have ht : (1/2 : ℝ)-1 = -(1/2 : ℝ) := by norm_num
  have hMIndex (a b : ℝ) (hab : a = b) :
      (sphereSobolevLinearCoordinateMulL hF hO hD a d :
        SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) =
      sphereSobolevLinearCoordinateMulL hF hO hD b d := by
    cases hab
    rfl
  have hIIndex (a b : ℝ) (hab : a = b) (ha : a ≤ (1/2 : ℝ)) (hb : b ≤ (1/2 : ℝ)) :
      (sphereSobolevInclusionL (1/2 : ℝ) a ha :
        SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) =
      sphereSobolevInclusionL (1/2 : ℝ) b hb := by
    cases hab
    rfl
  have hOld : sphereSobolevLinearCoordinateMulL hF hO hD ((1/2 : ℝ)-1) d
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) u) -
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d u) =
      sphereSobolevInclusionL (1/2 : ℝ) ((1/2 : ℝ)-1) (by linarith)
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d u -
          sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d u) := by
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply] using h
  have hLeft := congrArg (fun M : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
    M (sphereSobolevShiftedDegreeL (1/2 : ℝ) u) -
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d u))
        (hMIndex ((1/2 : ℝ)-1) (-(1/2 : ℝ)) ht)
  have hRight := congrArg (fun I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
    I (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d u -
      sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d u)) (hIIndex ((1/2 : ℝ)-1) (-(1/2 : ℝ)) ht (by linarith) (by norm_num))
  exact hLeft.symm.trans (hOld.trans hRight)

lemma sphereSobolevDualPairing_radialDrift_adjoint_defect_skew
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (u : SphereSobolev s) (v : SphereSobolev (-s)) :
    sphereSobolevDualPairing s
      ((sphereSobolevRadialDriftAdjointL hF hO hD s d - sphereSobolevRadialDriftL hF hO hD s d) u) v =
      -sphereSobolevDualPairing s u
        ((sphereSobolevRadialDriftAdjointL hF hO hD (-s) d - sphereSobolevRadialDriftL hF hO hD (-s) d) v) := by
  have hFirst := sphereSobolevDualPairing_radialDriftAdjoint hF hO hD s d u v
  have hIndex : sphereSobolevRadialDriftAdjointL hF hO hD (-s) d =
      ContinuousLinearMap.adjoint (sphereSobolevRadialDriftL hF hO hD s d) := by
    unfold sphereSobolevRadialDriftAdjointL
    have hEqualIndex (a b : ℝ) (hab : a = b) :
        (sphereSobolevRadialDriftL hF hO hD a d : SphereSobolev s →L[ℝ] SphereSobolev s) =
        sphereSobolevRadialDriftL hF hO hD b d := by
      cases hab
      rfl
    exact congrArg (fun A : SphereSobolev s →L[ℝ] SphereSobolev s => ContinuousLinearMap.adjoint A)
      (hEqualIndex (-(-s)) s (neg_neg s))
  have hSecond : sphereSobolevDualPairing s (sphereSobolevRadialDriftL hF hO hD s d u) v =
      sphereSobolevDualPairing s u (sphereSobolevRadialDriftAdjointL hF hO hD (-s) d v) := by
    exact (ContinuousLinearMap.adjoint_inner_right (sphereSobolevRadialDriftL hF hO hD s d) u v).symm.trans
      (congrArg (fun A : SphereSobolev s →L[ℝ] SphereSobolev s => inner ℝ u (A v)) hIndex.symm)
  have hLeft : sphereSobolevDualPairing s
      ((sphereSobolevRadialDriftAdjointL hF hO hD s d - sphereSobolevRadialDriftL hF hO hD s d) u) v =
      sphereSobolevDualPairing s (sphereSobolevRadialDriftAdjointL hF hO hD s d u) v -
        sphereSobolevDualPairing s (sphereSobolevRadialDriftL hF hO hD s d u) v := inner_sub_left _ _ _
  have hRight : -sphereSobolevDualPairing s u
      ((sphereSobolevRadialDriftAdjointL hF hO hD (-s) d - sphereSobolevRadialDriftL hF hO hD (-s) d) v) =
      -(sphereSobolevDualPairing s u (sphereSobolevRadialDriftAdjointL hF hO hD (-s) d v) -
        sphereSobolevDualPairing s u (sphereSobolevRadialDriftL hF hO hD (-s) d v)) :=
    congrArg (fun t : ℝ => -t) (inner_sub_right _ _ _)
  have hAlgebra (x y : ℝ) : x-y = -(y-x) := by ring
  exact hLeft.trans ((congrArg₂ (fun x y : ℝ => x-y) hFirst hSecond).trans
    ((hAlgebra _ _).trans hRight.symm))

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local irreducible] referenceLowerRadialEndpointFamily referenceSharpMidpointRadialTraceFamily
  sphereSobolevShiftedDegreeL sphereSobolevLinearCoordinateMulL
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,0)) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg s hs y hy
  have hMid := referenceSharpMidpointRadialTrace_zero_eq_degree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg s hs y hy
  have hInc := referenceSharpMidpointRadialTraceFamily_lower_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,0)) hp
  rw [hMid] at hInc
  apply sphereSobolev_clm_eq_of_single (1/2 : ℝ)
  intro k u
  have h := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
    A (sphereSobolevSingleL 1 k u)) hInc
  have hActual : (k : ℝ) • sphereSobolevSingleL (-(1/2 : ℝ)) k u =
      referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (s,(y,0)) (sphereSobolevSingleL (1/2 : ℝ) k u) := by
    simpa only [ContinuousLinearMap.comp_apply,sphereSobolevDegreeL_single,
      map_smul,sphereSobolevInclusionL_single] using h
  have hNative := sphereSobolevShiftedDegreeL_single (1/2 : ℝ) k u
  have ht : (1/2 : ℝ)-1 = -(1/2 : ℝ) := by norm_num
  rw [ht] at hNative
  exact hActual.symm.trans hNative.symm

lemma referenceLowerRadialEndpoint_zero_coordinate_commutator_eq_firstCorrection_defect
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (u : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (referenceCenterDrift g L s y)
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (s,(y,0)) u) -
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 (s,(y,0))
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L s y) u) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L s y) u -
       sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L s y) u) := by
  rw [referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg s hs y hy]
  exact sphereSobolevLinearCoordinateMul_half_degree_commutator hF hO hD (referenceCenterDrift g L s y) u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevLinearCoordinateMul_degree_commutator_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevLinearCoordinateMul_degree_commutator
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevLinearCoordinateMul_half_degree_commutator
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_radialDrift_adjoint_defect_skew
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialEndpoint_zero_coordinate_commutator_eq_firstCorrection_defect
