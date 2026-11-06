import Calderon.ActualHigherSPhysicalPairing
import Calderon.ActualAngularMixedEndpointPrimitives
import Calderon.ActualFinitePhysicalModelErrorDictionary

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFiniteCoreLoweringRealization
open SphereHarmonic SphereHilbertDecomposition ActualFiniteHarmonicCore AngularShiftGraph
  ActualAngularHighDraft ActualAngularPiDraft ActualHigherSPhysicalPairing

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I30" => sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
local notation "I10" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "ZE" => sphereSobolevZeroEquiv hO hD

/-- Every harmonic single is decoded exactly, including degree zero. -/
theorem halfToSphereL2_high_single (k : ℕ) (v : harmonicSphereSubspace k) :
    KL (IH (sphereSobolevSingleL (3/2 : ℝ) k v)) = (v : SphereL2) := by
  apply (ZE).injective
  rw [zeroEquiv_halfToSphereL2 hO hD,
    sphereSobolevInclusionL_single, sphereSobolevInclusionL_single]
  exact (sphereSobolevZeroEquiv_harmonic_subtype hO hD k v).symm

private theorem high_single_zero_decode (k : ℕ) (v : harmonicSphereSubspace k) :
    (ZE).symm (I30 (sphereSobolevSingleL (3/2 : ℝ) k v)) = (v : SphereL2) := by
  rw [sphereSobolevInclusionL_single,
    ← sphereSobolevZeroEquiv_harmonic_subtype hO hD k v]
  exact (ZE).symm_apply_apply _

/-- The actual all-output lowering operator realizes the original finite-core derivative. -/
theorem loweringHigh_finiteCore_decode (hF : SphereFischerInner)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (i : Fin 3) :
    KL (loweringHigh hF hO hD i
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y)) =
      (coreDerivative hO hD hF i F).val y := by
  let u : Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) F y
  let a : SphereL2 := KL (loweringHigh hF hO hD i u)
  let b : SphereL2 := (coreDerivative hO hD hF i F).val y
  have hHarmonic (k : ℕ) (v : harmonicSphereSubspace k) :
      ⟪a,(v : SphereL2)⟫_ℝ = ⟪b,(v : SphereL2)⟫_ℝ := by
    let t : Hi := sphereSobolevSingleL (3/2 : ℝ) k v
    have hDecode : KL (IH t) = (v : SphereL2) :=
      halfToSphereL2_high_single hO hD k v
    have hRaising := sphereSobolevAngularCoordinateTransposeL_threeHalf_raisingGraph
      hF hO hD i t
    change ((ZE).symm (I30 t),KL (raisingHigh hF hO hD i t)) ∈
      sphereRaisingGraph hF hO hD i at hRaising
    have hZero : (ZE).symm (I30 t) = (v : SphereL2) :=
      high_single_zero_decode hO hD k v
    rw [hZero] at hRaising
    have hAdjoint := sphereDerivativeGraph_inner_adjoint hF hO hD i
      (F.val y) b (v : SphereL2) (KL (raisingHigh hF hO hD i t))
      (coreDerivative_graph hO hD hF i F y) hRaising
    have hPair := v017_aA2 hF hO hD i u (IH t)
    have hShift := congrArg (fun z => PP (IH u) z)
      (v017_inclusion_raisingHigh hF hO hD i t).symm
    have hLeft := halfPairing_eq_inner_sphereL2 hO hD
      (loweringHigh hF hO hD i u) (IH t)
    have hRight := halfPairing_eq_inner_sphereL2 hO hD
      (IH u) (raisingHigh hF hO hD i t)
    have hNative : KL (IH u) = F.val y :=
      halfToSphereL2_finiteCoreLift hO hD F y
    calc
      ⟪a,(v : SphereL2)⟫_ℝ = ⟪a,KL (IH t)⟫_ℝ :=
        (congrArg (fun z : SphereL2 => ⟪a,z⟫_ℝ) hDecode).symm
      _ = ⟪KL (IH u),KL (raisingHigh hF hO hD i t)⟫_ℝ :=
        hLeft.symm.trans (hPair.trans (hShift.trans hRight))
      _ = ⟪F.val y,KL (raisingHigh hF hO hD i t)⟫_ℝ :=
        congrArg (fun z : SphereL2 => ⟪z,KL (raisingHigh hF hO hD i t)⟫_ℝ) hNative
      _ = ⟪b,(v : SphereL2)⟫_ℝ := hAdjoint.symm
  apply ext_inner_right ℝ
  intro v
  have hSeries := hasSum_sphereHarmonicDecomposition hO hD v
  have hA := (innerSL ℝ a).hasSum hSeries
  have hB := (innerSL ℝ b).hasSum hSeries
  have hTerms : (fun k : ℕ => ⟪a,((sphereHarmonicDecomposition hO hD v) k : SphereL2)⟫_ℝ) =
      (fun k : ℕ => ⟪b,((sphereHarmonicDecomposition hO hD v) k : SphereL2)⟫_ℝ) :=
    funext (fun k => hHarmonic k ((sphereHarmonicDecomposition hO hD v) k))
  change HasSum (fun k : ℕ =>
    ⟪a,((sphereHarmonicDecomposition hO hD v) k : SphereL2)⟫_ℝ) ⟪a,v⟫_ℝ at hA
  change HasSum (fun k : ℕ =>
    ⟪b,((sphereHarmonicDecomposition hO hD v) k : SphereL2)⟫_ℝ) ⟪b,v⟫_ℝ at hB
  rw [hTerms] at hA
  exact hA.unique hB

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFiniteCoreLoweringRealization
