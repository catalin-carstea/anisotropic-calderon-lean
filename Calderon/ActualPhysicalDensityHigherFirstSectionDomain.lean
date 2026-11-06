import Calderon.ActualPhysicalDensityOperator
import Calderon.SphereSobolevCoordinateInclusion

/-! Internal local-section implication; the eta construction is elsewhere. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceLowerDensityFirstAction referenceLowerHorizontalAction
  referenceHighDensityFirstAction referenceHighHorizontalAction referencePhysicalDensityOperator
  referenceDensityCovariantSecondAction referenceLowerAdjointMovingBoundaryActionFamily
  referenceHighHorizontalAngularL referenceLowerHorizontalAngularL referenceMetricGramFrame
  referenceFrameConnectionCoefficient sphereSobolevInclusionL referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint

lemma referenceLowerDensityFirstAction_congr_of_eventuallyEq
    (q : ℝ) (R : R3 → ℝ) (v wv : R3 → SphereSobolev (1/2 : ℝ))
    (y : R3) (i : Fin 3) (h : v =ᶠ[𝓝 y] wv) :
    referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i =
      referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R wv y i := by
  unfold referenceLowerDensityFirstAction referenceLowerHorizontalAction
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let e := referenceMetricGramFrame g L (q,y) i
  let Ω := referenceLowerHorizontalAngularL g L q y i
  let C := referenceLowerAdjointMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i
  have hD := congrArg (fun A : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) => J (A e)) h.fderiv_eq
  have hΩ := congrArg Ω h.self_of_nhds
  have hC := congrArg C h.self_of_nhds
  exact congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z+t)
    (congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z+t) hD hΩ) hC

lemma referenceDensityCovariantSecondAction_half_graph_of_local_high_firstSections
    (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (η : Fin 3 → R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i j : Fin 3)
    (hη : ∀ k : Fin 3, ContDiffAt ℝ ∞ (η k) y)
    (hEq : ∀ k : Fin 3,
      (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (η k x)) =ᶠ[𝓝 y]
      (fun x => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x k))
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i -
        ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j •
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (η k y)) =
    referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Γ : Fin 3 → ℝ := fun k => referenceFrameConnectionCoefficient
    g L q y (referenceMetricGramFrame g L (q,y) i) k j
  have hFirst := (referenceDensityFirstAction_high_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R y i hInv hWeak (η j)
      ((hη j).differentiableAt (by simp))).trans
    (referenceLowerDensityFirstAction_congr_of_eventuallyEq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R _ _ y i (hEq j))
  have hConnection : J (∑ k : Fin 3, Γ k • I (η k y)) =
      ∑ k : Fin 3, Γ k • J
        (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y k) := by
    calc
      _ = ∑ k : Fin 3, Γ k • J (I (η k y)) := by simp only [map_sum,map_smul]
      _ = _ := Finset.sum_congr rfl (fun k _ =>
        congrArg (fun z : SphereSobolev (1/2 : ℝ) => Γ k • J z) (hEq k).self_of_nhds)
  have hLinear := (J.map_sub _ _).trans
    (congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z-t) hFirst hConnection)
  have hLiteral : referenceDensityCovariantSecondAction
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j =
      referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun x => referenceHighDensityFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x j) y i -
      ∑ k : Fin 3, Γ k • J
        (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y k) := by
    unfold referenceDensityCovariantSecondAction
    rfl
  exact hLinear.trans hLiteral.symm

lemma exists_referencePhysicalDensityOperator_half_of_local_high_firstSections
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (η : Fin 3 → R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (hη : ∀ k : Fin 3, ContDiffAt ℝ ∞ (η k) y)
    (hEq : ∀ k : Fin 3,
      (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (η k x)) =ᶠ[𝓝 y]
      (fun x => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x k))
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    ∃ v : SphereSobolev (1/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v =
      referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let V : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) := fun i j =>
    referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) y i -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j • I (η k y)
  let v : SphereSobolev (1/2 : ℝ) := R y •
    ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j • V i j) +
      ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • I (η i y))
  have hSecond (i j : Fin 3) : J (V i j) =
      referenceDensityCovariantSecondAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j :=
    referenceDensityCovariantSecondAction_half_graph_of_local_high_firstSections
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R u η y i j hη hEq hInv hWeak
  have hFirst (i : Fin 3) : J (I (η i y)) = J
      (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) :=
    congrArg J (hEq i).self_of_nhds
  refine ⟨v,?_⟩
  have hLinear : J v = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j • J (V i j)) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J (I (η i y))) := by
    simp only [v,map_smul,map_add,map_sum]
  have hTransport : R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j • J (V i j)) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J (I (η i y))) = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        referenceDensityCovariantSecondAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J
          (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i)) :=
    congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z)
    (congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z+t)
      (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
          referenceDensityPrincipalFrameCoefficient g g2 L q y i j • z) (hSecond i j))))
      (Finset.sum_congr rfl (fun i _ => congrArg
        (fun z : SphereSobolev (-(1/2 : ℝ)) => normalizedSecondDriftFrameJoint g g2 L i (q,y) • z) (hFirst i))))
  have hLiteral : referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y = R y •
      ((∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        referenceDensityCovariantSecondAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i j) +
        ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J
          (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i)) := by
    unfold referencePhysicalDensityOperator
    rfl
  exact hLinear.trans (hTransport.trans hLiteral.symm)

lemma exists_referencePhysicalDensityOperator_L2_of_local_high_firstSections
    (g2 : MatrixField) (hreg : FixedDirichletRegularity) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (η : Fin 3 → R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (hη : ∀ k : Fin 3, ContDiffAt ℝ ∞ (η k) y)
    (hEq : ∀ k : Fin 3,
      (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (η k x)) =ᶠ[𝓝 y]
      (fun x => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u x k))
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible) :
    ∃ v : SphereL2,
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v) =
      referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y := by
  obtain ⟨v,hv⟩ := exists_referencePhysicalDensityOperator_half_of_local_high_firstSections
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hreg q R u η y hη hEq hInv hWeak
  let Z := sphereSobolevZeroEquiv hO hD
  let v0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v
  refine ⟨Z.symm v0,?_⟩
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) (Z.apply_symm_apply v0)
  have hTrans := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  exact hCancel.trans (hTrans.trans hv)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerDensityFirstAction_congr_of_eventuallyEq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantSecondAction_half_graph_of_local_high_firstSections
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePhysicalDensityOperator_half_of_local_high_firstSections
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePhysicalDensityOperator_L2_of_local_high_firstSections
