import Calderon.ActualTSActualTriplePhysicalCaps
import Calderon.ActualTSZeroFirstScalarJets
import Calderon.ActualHigherSScalarCommutatorCoefficients

/-! Actual weighted coefficients for the 270 original zero-T/first-S triples. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstBilinearCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation
  ActualTSActualTripleRoomCaps ActualTSActualTriplePhysicalCaps ActualTSTripleBilinearCoefficient
  ActualTSZeroFirstScalarJets ActualHigherSMixedWordScalarJets
  ActualHigherSScalarCommutatorCoefficients PrincipalCommutator
  ActualScalarPrincipalAdjoint ActualRetainedGeneratorMultiplierGains

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Coeff" => TripleCoefficientSpace
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local instance] tripleCoefficientNormedGroup tripleCoefficientNormedSpace
  spatialTripleCoefficientNormedGroup spatialTripleCoefficientNormedSpace
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QC" => actualTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "Tq" => ActualHigherSFormation.higherSParam L

/-- The identical original scalar multiplies its original ordered D01 triple. -/
def zeroFirstWeightedTripleCoefficient (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (k j i : Fin 3) (V : Generator) (x : R3) : Coeff :=
  zeroFirstWordWeight g L g2 q dr Ar p k j i V x •
    QC ((Tq dr Ar p q) x) (Sum.inl j) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V))
local notation "WCoeff" => zeroFirstWeightedTripleCoefficient
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Input order agrees literally with the original half/negative triple. -/
theorem zeroFirstWeightedTripleCoefficient_apply
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (k j i : Fin 3) (V : Generator) (x : R3) (u v : Hi) :
    WCoeff g2 q dr Ar p k j i V x u v =
      zeroFirstWordWeight g L g2 q dr Ar p k j i V x *
        PL (AH ((Tq dr Ar p q) x) (Sum.inl j) v)
          (AL ((Tq dr Ar p q) x) (Sum.inr (Sum.inr i))
            (AH ((Tq dr Ar p q) x) (Sum.inr (Sum.inl V)) u)) := rfl

attribute [local irreducible] actualTripleCoefficient ActualHigherSFormation.higherSParam

/-- All constants precede profiles. Smoothness and genuine coordinate derivative
caps are produced for exactly the original 270 scalar/atom combinations. -/
theorem exists_actual_uniform_zero_first_weighted_triple_first_caps
    (hL : 0 < L) {d : ℝ} (hd : 0 < d) (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cweight : ℝ, 0 < Cweight ∧ ∃ etaRoom : ℝ, 0 < etaRoom ∧ etaRoom ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRoom →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ k j i : Fin 3, ∀ V : Generator,
      ContDiffAt ℝ ∞ (WCoeff g2 q dr Ar p k j i V) x ∧
        ‖WCoeff g2 q dr Ar p k j i V x‖ ≤ Cweight*eta ∧
        ∀ m : Fin 3, ‖directionalFDeriv (coordinateDirection m)
          (WCoeff g2 q dr Ar p k j i V) x‖ ≤ Cweight*eta := by
  let physicalWitness := exists_actual_uniform_triple_physical_first_caps
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hd P
  let Cphys : ℝ := Classical.choose physicalWitness
  have hCphys : 0 < Cphys := (Classical.choose_spec physicalWitness).1
  let thresholdWitness := (Classical.choose_spec physicalWitness).2
  let etaRoom : ℝ := Classical.choose thresholdWitness
  have hEta : 0 < etaRoom := (Classical.choose_spec thresholdWitness).1
  have hEta1 : etaRoom ≤ 1 := (Classical.choose_spec thresholdWitness).2.1
  have hPhysical := (Classical.choose_spec thresholdWitness).2.2
  obtain ⟨Cs,hCs,hScalar⟩ := exists_actual_zero_first_word_scalar_first_caps g hg L hL y0 ρ g2 hg2
  let Cweight : ℝ := 2*Cs*Cphys+1
  have hCweight : 0 < Cweight := by dsimp only [Cweight]; positivity
  have hSC : 0 ≤ Cs*Cphys := mul_nonneg hCs.le hCphys.le
  have hC0 : Cs*Cphys ≤ Cweight := by dsimp only [Cweight]; nlinarith only [hSC]
  have hC1 : 2*Cs*Cphys ≤ Cweight := by dsimp only [Cweight]; linarith
  refine ⟨Cweight,hCweight,etaRoom,hEta,hEta1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x hx hxBall hb hs k j i V
  let s : R3 → ℝ := zeroFirstWordWeight g L g2 q dr Ar p k j i V
  let A : R3 → Coeff := fun y => QC ((Tq dr Ar p q) y)
    (Sum.inl j) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V))
  have hJet := hScalar q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaRoom.trans hEta1) x hx hb hs k j i V
  have hAPredicate := hPhysical q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x hx hxBall hb hs
    (Sum.inl j) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V))
  have hA : ContDiffAt ℝ ∞ A x ∧ ‖A x‖ ≤ Cphys ∧ ‖fderiv ℝ A x‖ ≤ Cphys :=
    (physicalTripleFirstCaps_iff A x Cphys).mp hAPredicate
  have hsSmooth : ContDiffAt ℝ ∞ s x :=
    (contDiff_zeroFirstWordWeight g hg L g2 hg2 q dr Ar p hdr hAr k j i V).contDiffAt
  have hS0 : |s x| ≤ Cs*eta := hJet.value
  have hS1 (m : Fin 3) : |directionalFDeriv (coordinateDirection m) s x| ≤ Cs*eta := by
    have h := (fderiv ℝ s x).le_opNorm (coordinateDirection m)
    have hCoord : ‖directionalFDeriv (coordinateDirection m) s x‖ ≤ ‖fderiv ℝ s x‖ := by
      simpa only [directionalFDeriv,norm_coordinateDirection,mul_one] using h
    simpa only [Real.norm_eq_abs] using hCoord.trans hJet.derivative
  have hA1 (m : Fin 3) : ‖directionalFDeriv (coordinateDirection m) A x‖ ≤ Cphys := by
    have h := (fderiv ℝ A x).le_opNorm (coordinateDirection m)
    have hCoord : ‖directionalFDeriv (coordinateDirection m) A x‖ ≤ ‖fderiv ℝ A x‖ := by
      simpa only [directionalFDeriv,norm_coordinateDirection,mul_one] using h
    exact hCoord.trans hA.2.2
  have hValue : ‖s x • A x‖ ≤ Cweight*eta := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (Cs*eta)*Cphys := mul_le_mul hS0 hA.2.1 (norm_nonneg _) (mul_nonneg hCs.le heta)
      _ = (Cs*Cphys)*eta := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC0 heta
  have hSmooth : ContDiffAt ℝ ∞ (fun y => s y • A y) x := hsSmooth.smul hA.1
  refine ⟨hSmooth,hValue,?_⟩
  intro m
  have hProd := product_first_jet_budget s A x (coordinateDirection m) hsSmooth hA.1
    (Cs*eta) (Cs*eta) Cphys Cphys (by positivity) (by positivity) hCphys.le hCphys.le
    hS0 (hS1 m) hA.2.1 (hA1 m)
  calc
    _ ≤ (Cs*eta)*Cphys+(Cs*eta)*Cphys := hProd.2
    _ = (2*Cs*Cphys)*eta := by ring
    _ ≤ Cweight*eta := mul_le_mul_of_nonneg_right hC1 heta

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstBilinearCaps
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstBilinearCaps.zeroFirstWeightedTripleCoefficient_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstBilinearCaps.exists_actual_uniform_zero_first_weighted_triple_first_caps
