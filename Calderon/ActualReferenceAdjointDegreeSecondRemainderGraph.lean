import Calderon.ActualReferenceDegreeSecondRemainderRawGraph
import Calderon.ActualReferenceSignedRemainderPivot
import Calderon.NativeRadialJetTranspose
import Calderon.SphereSobolevDualOrthogonalPullback
import Mathlib.Topology.DenseEmbedding

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

lemma neg_transpose_referenceRadialDegreeCommutatorHalfSecondRemainder_genuine_adjoint_graph
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Bhigh := sphereSobolevShiftedDegreeL (3/2 : ℝ)
    let Bhalf := sphereSobolevShiftedDegreeL (1/2 : ℝ)
    let C2 := referenceRadialDegreeCommutatorHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    let Th := secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
    let Tl := secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
    ∀ u : SphereSobolev (3/2 : ℝ),
      (-sphereLowerDistributionalTranspose C2) (I u) =
        Bhalf (Th u) - Tl (Bhigh u) := by
  intro I Bhigh Bhalf C2 Th Tl
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Sh := referenceSharpRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let Sl := referenceLowerRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let P : SphereSobolev (-(1/2 : ℝ)) → SphereSobolev (1/2 : ℝ) → ℝ :=
    fun v z => sphereSobolevDualPairing (-(1/2 : ℝ)) v z
  let Q : SphereSobolev (1/2 : ℝ) → SphereSobolev (-(1/2 : ℝ)) → ℝ :=
    fun z v => sphereSobolevDualPairing (1/2 : ℝ) z v
  have hFlip (v : SphereSobolev (-(1/2 : ℝ))) (z : SphereSobolev (1/2 : ℝ)) :
      Q z v = P v z := (real_inner_comm z v).symm
  have hSub (z : SphereSobolev (1/2 : ℝ))
      (v w : SphereSobolev (-(1/2 : ℝ))) : Q z (v-w) = Q z v-Q z w :=
    inner_sub_right z v w
  have hBTranspose : sphereLowerDistributionalTranspose Bhalf = Bhalf :=
    sphereLowerDistributionalTranspose_shiftedDegree_half
  have hDegree (v : SphereSobolev (3/2 : ℝ)) : J (Bhigh v) = Bhalf (I v) :=
    congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      sphereSobolevShiftedDegree_high_half_compatibility
  have hBPair (v : SphereSobolev (3/2 : ℝ)) (z : SphereSobolev (1/2 : ℝ)) :
      Q (I v) (Bhalf z) = ⟪Z (Bhigh v),Z z⟫_ℝ := by
    calc
      _ = Q z (sphereLowerDistributionalTranspose Bhalf (I v)) :=
        sphereSobolevDualPairing_lower_distributionalTranspose Bhalf z (I v)
      _ = Q z (Bhalf (I v)) := congrArg (fun A => Q z (A (I v))) hBTranspose
      _ = Q z (J (Bhigh v)) := congrArg (Q z) (hDegree v).symm
      _ = P (J (Bhigh v)) z := hFlip _ _
      _ = _ := sphereSobolevDualPairing_inclusion_eq_inner_zero
        (1/2 : ℝ) (by norm_num) (Bhigh v) z
  have hPivot := referenceRadialSecondRemainder_genuine_pivot_pairings
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hSPair (z : SphereSobolev (1/2 : ℝ)) (v : SphereSobolev (3/2 : ℝ)) :
      Q (I v) (Sl z) = ⟪Z z,Z (Th v)⟫_ℝ := (hFlip _ _).trans (hPivot.1 z v)
  have hTPair (z : SphereSobolev (1/2 : ℝ)) (v : SphereSobolev (3/2 : ℝ)) :
      Q (I v) (Tl z) = ⟪Z z,Z (Sh v)⟫_ℝ := (hFlip _ _).trans (hPivot.2 z v)
  have hRaw := referenceRadialDegreeCommutatorHalfSecondRemainder_raw_degree_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSegment
  intro u
  have hTest (v : SphereSobolev (3/2 : ℝ)) :
      Q (I v) (sphereLowerDistributionalTranspose C2 (I u)) =
        Q (I v) (Tl (Bhigh u)-Bhalf (Th u)) := by
    calc
      _ = Q (I u) (C2 (I v)) :=
        (sphereSobolevDualPairing_lower_distributionalTranspose C2 (I v) (I u)).symm
      _ = Q (I u) (Bhalf (Sh v)-Sl (Bhigh v)) := congrArg (Q (I u)) (hRaw v)
      _ = Q (I u) (Bhalf (Sh v))-Q (I u) (Sl (Bhigh v)) := hSub _ _ _
      _ = ⟪Z (Bhigh u),Z (Sh v)⟫_ℝ-⟪Z (Bhigh v),Z (Th u)⟫_ℝ :=
        congrArg₂ (fun a b : ℝ => a-b) (hBPair u (Sh v)) (hSPair (Bhigh v) u)
      _ = Q (I v) (Tl (Bhigh u))-Q (I v) (Bhalf (Th u)) :=
        congrArg₂ (fun a b : ℝ => a-b) (hTPair (Bhigh u) v).symm (hBPair v (Th u)).symm
      _ = _ := (hSub _ _ _).symm
  let Ltest : SphereSobolev (1/2 : ℝ) → ℝ :=
    fun z => Q z (sphereLowerDistributionalTranspose C2 (I u))
  let Rtest : SphereSobolev (1/2 : ℝ) → ℝ :=
    fun z => Q z (Tl (Bhigh u)-Bhalf (Th u))
  have hLtest : Continuous Ltest := continuous_id.inner continuous_const
  have hRtest : Continuous Rtest := continuous_id.inner continuous_const
  have hTests : Ltest ∘ I = Rtest ∘ I := funext hTest
  have hAll : Ltest = Rtest :=
    (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).equalizer
      hLtest hRtest hTests
  have hPositive : sphereLowerDistributionalTranspose C2 (I u) =
      Tl (Bhigh u)-Bhalf (Th u) :=
    sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ) _ _ (fun z => congrFun hAll z)
  change -(sphereLowerDistributionalTranspose C2 (I u)) = _
  exact (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => -z) hPositive).trans
    (neg_sub _ _)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.neg_transpose_referenceRadialDegreeCommutatorHalfSecondRemainder_genuine_adjoint_graph
