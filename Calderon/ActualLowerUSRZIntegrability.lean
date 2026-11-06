import Calderon.ActualLowerUSOrdinaryRows

/-! Individual actual native R/Z integrability, with no cap premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSRZIntegrability
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSFirstOutput ActualHigherSFirstPhysicalCommutatorGraph
  ActualHigherSZeroPhysicalGraph ActualLowerUSSignedRows ActualLowerUSGainedDQ
  ActualLowerUSOrdinaryRows ActualHigherSScalarCommutatorForm ActualModelCommutatorWords

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)


local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "dd" i:max => coreDirectionalDerivative hO hD (coordinateDirection i)

private lemma integrable_pointwise_sub (f g : R3 → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => f x-g x) := by
  simpa only [Pi.sub_def] using hf.sub hg

private lemma integrable_pointwise_add (f g : R3 → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => f x+g x) := by
  simpa only [Pi.add_def] using hf.add hg

include hg in
/-- Every weighted native inner product with a genuine finite compact test
is integrable whenever its physical output is continuous. -/
private lemma weighted_finite_test_integrable (q : ℝ) (F : FC) (v : R3 → SphereL2)
    (hv : Continuous v) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,v x⟫_ℝ) := by
  have hm : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    ((contDiff_referenceDensityFamily g hg L).comp
    (contDiff_const.prodMk contDiff_id)).continuous
  apply (hm.mul (F.property.1.continuous.inner hv)).integrable_of_hasCompactSupport
  apply F.property.2.1.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  change referenceDensityFamily g L (q,x)*⟪F.val x,v x⟫_ℝ = 0
  rw [hzero,inner_zero_left,mul_zero]

private lemma support_coefficientDerivative (A : Module.End ℝ FC)
    (hA : FiniteCoreSupportPreserving hO hD A) (i : Fin 3) :
    FiniteCoreSupportPreserving hO hD (coefficientDerivative (dd i) A) := by
  unfold coefficientDerivative ActualModelCommutatorWords.commutator
  exact finiteCoreSupportPreserving_sub hO hD _ _
    (finiteCoreSupportPreserving_mul hO hD _ _
      (finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _) hA)
    (finiteCoreSupportPreserving_mul hO hD _ _ hA
      (finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _))

/-- Separate integrability of the literal first and zero rows, with full S
outputs retained and every finite pre-input supported in the same native room. -/
theorem nativeRZ_integrable_of_common_room
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (δ : ℝ) (Cm : CRoom δ) (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom δ) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      nativeRFirstDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F x) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      nativeZZeroDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F x) := by
  let D := nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  let BN := nativeB hO hD hF g g2 hg L q dr Ar p
  let J := nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  let Js := nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  let P := nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
  let Q := nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  have hDS (i : Fin 3) : FiniteCoreSupportPreserving hO hD (D i) :=
    finiteCoreSupportPreserving_nativeULowerAdjointFirstCoefficient
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i
  have hJS : FiniteCoreSupportPreserving hO hD J :=
    finiteCoreSupportPreserving_nativeULowerAdjointZeroCoefficient
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  have hddS (i : Fin 3) : FiniteCoreSupportPreserving hO hD (dd i) :=
    finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _
  have hRoom (G : FC) (hG : tsupport G.val ⊆ tsupport F.val) :
      ∀ x ∈ tsupport G.val, (Tq dr Ar p q) x ∈ ParamRoom δ :=
    fun x hx => hTF x (hG hx)
  have hP (j : Fin 3) (G : FC) (hG : tsupport G.val ⊆ tsupport F.val) :
      ContDiff ℝ ∞ (P j G) :=
    nativeFirstOut_contDiff_of_common_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm g2 hg2 dr Ar p hdr hAr q j G (hRoom G hG)
  have hQ (G : FC) (hG : tsupport G.val ⊆ tsupport F.val) : ContDiff ℝ ∞ (Q G) :=
    (nativeZeroOut_regular g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq G (hRoom G hG)).1
  have hPair (U : FC) (v : R3 → SphereL2) (hv : ContDiff ℝ ∞ v) :
      Integrable (fun x => mu x*⟪U.val x,v x⟫_ℝ) :=
    weighted_finite_test_integrable (g := g) (L := L) (hg := hg) (hO := hO) (hD := hD) q U v hv.continuous
  have hOrdR (i j : Fin 3) : Integrable (fun x => mu x*nativeOrdinaryRRow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q i j F x) := by
    have hV := hddS j F
    have hC := support_coefficientDerivative hO hD (D j) (hDS j) i ((dd j) F)
    have hDP := nativeDerivativePOutput_contDiff_of_common_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm g2 hg2 dr Ar p hdr hAr q i j ((dd j) F) (hRoom _ hV)
    have ha := hPair (-(BN i hg2 hdr hAr F)) _ hDP
    have hb := hPair F _ (hP i _ (hC.trans hV))
    simpa only [nativeOrdinaryRRow,mu,D,BN,P,mul_sub,Submodule.coe_neg,Pi.neg_apply] using
      integrable_pointwise_sub _ _ ha hb
  have hDQ (j : Fin 3) : Integrable (fun x => mu x*nativeDZeroCommutatorDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q j F ((dd j) F) x) := by
    have hV := hddS j F
    have ha := hPair (-(BN j hg2 hdr hAr F)) _ (hQ _ hV)
    have hb := hPair F _ (hQ _ ((hDS j ((dd j) F)).trans hV))
    simpa only [nativeDZeroCommutatorDensity,mu,D,BN,Q,mul_sub,Submodule.coe_neg,Pi.neg_apply] using
      integrable_pointwise_sub _ _ ha hb
  have hJP (j : Fin 3) : Integrable (fun x => mu x*
      (⟪(Js F).val x,P j ((dd j) F) x⟫_ℝ-⟪F.val x,P j (J ((dd j) F)) x⟫_ℝ)) := by
    have hV := hddS j F
    simpa only [mul_sub] using integrable_pointwise_sub _ _ (hPair (Js F) _ (hP j _ hV))
      (hPair F _ (hP j _ ((hJS ((dd j) F)).trans hV)))
  have hOrdZ (i : Fin 3) : Integrable (fun x => mu x*nativeOrdinaryZRow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q i F x) := by
    have hC := support_coefficientDerivative hO hD J hJS i F
    have hDQ := nativeDerivativeQOutput_contDiff_of_common_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq i F hTF
    have ha := hPair (-(BN i hg2 hdr hAr F)) _ hDQ
    have hb := hPair F _ (hP i _ hC)
    simpa only [nativeOrdinaryZRow,mu,J,BN,P,mul_sub,Submodule.coe_neg,Pi.neg_apply] using
      integrable_pointwise_sub _ _ ha hb
  have hJQ : Integrable (fun x => mu x*(⟪(Js F).val x,Q F x⟫_ℝ-⟪F.val x,Q (J F) x⟫_ℝ)) := by
    simpa only [mul_sub] using integrable_pointwise_sub _ _ (hPair (Js F) _ (hQ F Subset.rfl))
      (hPair F _ (hQ _ (hJS F)))
  constructor
  · have hSum (j : Fin 3) : Integrable (fun x =>
        (∑ i : Fin 3, mu x*nativeOrdinaryRRow
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q i j F x)+
        mu x*nativeDZeroCommutatorDensity
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
          g2 hg2 dr Ar p hdr hAr q j F ((dd j) F) x+
        mu x*(⟪(Js F).val x,P j ((dd j) F) x⟫_ℝ-⟪F.val x,P j (J ((dd j) F)) x⟫_ℝ)) :=
      integrable_pointwise_add _ _
        (integrable_pointwise_add _ _ (integrable_finset_sum _ (fun i _ => hOrdR i j)) (hDQ j)) (hJP j)
    simpa only [nativeRFirstDensity,Finset.mul_sum,mul_add,mu,Js,P,J,Pi.add_apply] using
      integrable_finset_sum _ (fun j _ => hSum j)
  · simpa only [nativeZZeroDensity,Finset.mul_sum,mul_add,mu,Js,P,J,Q,Pi.add_apply] using
      integrable_pointwise_add _ _ (integrable_finset_sum _ (fun i _ => hOrdZ i)) hJQ

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSRZIntegrability
