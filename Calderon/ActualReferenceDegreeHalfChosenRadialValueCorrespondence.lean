import Calderon.ActualReferenceDegreeCommutatorHighJetBlock
import Calderon.ActualReferenceDegreeHalfChosenSmoothness
import Calderon.DenseOperatorCanonicalRadialTaylorGraph
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError DenseOperatorTaylorGraph
/-! The first and signed-remainder values of the chosen half family coincide
with the canonical named values. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceRadialDegreeCommutatorHalfFamily
  referenceRadialDegreeCommutatorHighL sphereSobolevInclusionL
include hreg

lemma referenceRadialDegreeCommutatorHalfFirstFamily_eq_chosen_deriv
    (q : ℝ) (y : R3) (hp : (q,(y,(0:ℝ))) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceRadialDegreeCommutatorHalfFirstFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y =
      deriv (fun r : ℝ => referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) 0 := by
  let I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hIdentity : ∀ p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0,
      (referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp I = referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := by
    intro p hp
    apply ContinuousLinearMap.ext
    intro u
    exact referenceRadialDegreeCommutatorHalfFamily_high_graph_on_locus g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp u
  have hGeneric := deriv_operator_radial_high_graph
    (Q := ℝ) (P := R3) (E := SphereSobolev (3/2:ℝ))
    (G := SphereSobolev (1/2:ℝ)) (V := SphereSobolev (-(1/2:ℝ)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  have hOperator : (deriv (fun r : ℝ => referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) 0).comp I =
      deriv (fun r : ℝ => referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) 0 := by
    try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq]
    exact hGeneric (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) I
      (referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) hIdentity q y 0 hp
      (contDiffAt_referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,0)) hp)
      (contDiffAt_referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp)
  have hCanonical := extendOfNorm_eq_of_dense_operator_graph
    (E := SphereSobolev (3/2:ℝ)) (G := SphereSobolev (1/2:ℝ)) (V := SphereSobolev (-(1/2:ℝ)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hCanonical
  have hResult := hCanonical I
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (deriv (fun r : ℝ => referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) 0)
    (deriv (fun r : ℝ => referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) 0)
    (fun u => congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) hOperator)
  simpa only [referenceRadialDegreeCommutatorHalfFirstFamily,I] using hResult

lemma referenceRadialDegreeCommutatorHalfSecondRemainder_eq_chosen_remainder
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ t ∈ Icc (0:ℝ) 1, (q,(y,t*r)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceRadialDegreeCommutatorHalfSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r =
      secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r := by
  let I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hIdentity : ∀ p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0,
      (referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp I = referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := by
    intro p hp
    apply ContinuousLinearMap.ext
    intro u
    exact referenceRadialDegreeCommutatorHalfFamily_high_graph_on_locus g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp u
  have hGeneric := secondTaylorRemainder_operator_radial_high_graph
    (Q := ℝ) (P := R3) (E := SphereSobolev (3/2:ℝ))
    (G := SphereSobolev (1/2:ℝ)) (V := SphereSobolev (-(1/2:ℝ)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  have hOperator : (secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).comp I =
      secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r := by
    try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq]
    exact hGeneric (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) I
      (referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) hIdentity
      (fun p hp => contDiffAt_referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp)
      (fun p hp => contDiffAt_referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp) q y r hSegment
  have hCanonical := extendOfNorm_eq_of_dense_operator_graph
    (E := SphereSobolev (3/2:ℝ)) (G := SphereSobolev (1/2:ℝ)) (V := SphereSobolev (-(1/2:ℝ)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hCanonical
  have hResult := hCanonical I
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r)
    (secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r)
    (fun u => congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) hOperator)
  simpa only [referenceRadialDegreeCommutatorHalfSecondRemainder,I] using hResult

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHalfFirstFamily_eq_chosen_deriv
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHalfSecondRemainder_eq_chosen_remainder
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
