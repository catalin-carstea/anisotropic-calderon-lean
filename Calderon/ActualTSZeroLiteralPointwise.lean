import Calderon.ActualTSZeroPhysicalPairing
import Calderon.ActualTSZeroLinearRemainder
import Calderon.ActualSZeroPhysicalWordDictionary

/-!
Literal signed T/S zero/zero POINTWISE assembly.
The original core-valued T/Tdag zero pair and the original S/Sdag zero remainders
are used, with factor4. Integrability and the integral are handled separately.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralPointwise
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTSZeroPhysicalPairing ActualTSZeroCorrectionQuadratic ActualTSZeroLinearRemainder
  ActualSZeroPhysicalWordDictionary ActualTZeroGenuineReverse ActualHigherSPhysicalPairing
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

private lemma three_piece_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (t td r z2 t2 z1 t1 s sd : V) (hs : s=z2+z1) (hsd : sd=t2+t1) :
    (4 : ℝ)*(⟪t,s⟫_ℝ-⟪td,sd⟫_ℝ) =
      4*(⟪t,z2⟫_ℝ-⟪r,t2⟫_ℝ)+(-4)*⟪td-r,t2⟫_ℝ+
        (4*⟪t,z1⟫_ℝ-4*⟪td,t1⟫_ℝ) := by
  rw [hs,hsd]
  simp only [inner_add_right,inner_sub_left]
  ring

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
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
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "T0" => rawForwardZeroHalf hF hO hD g L hg
local notation "Td0" => rawAdjointZeroHalf hF hO hD g L hg
local notation "RHalf" => genuineReferenceZeroReverseHalf hF hO hD g L
local notation "Z2" => ActualHigherSQuadraticZeroQuartic.actualZ2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "S0" => ActualHigherSZeroPhysicalGraph.nativeZeroHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
local notation "Sd0" => ActualSFirstPhysicalDictionary.nativeAdjointZeroHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
local notation "GD" => genuineQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "CD" => negativeCorrectionQuadraticDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "LD" => signedLinearZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Exactly four times the last pair in the original lowerPhysicalCross definition. -/
def originalZeroZeroCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*(⟪(nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x,
          KL (S0 g2 dr Ar p hdr hAr q F x)⟫_ℝ-
      ⟪(nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x,
          KL (Sd0 g2 dr Ar p hdr hAr q F x)⟫_ℝ)
local notation "D00" => originalZeroZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] originalZeroZeroCrossDensity genuineQuadraticZeroCrossDensity
  negativeCorrectionQuadraticDensity signedLinearZeroCrossDensity rawForwardZeroHalf rawAdjointZeroHalf
  ActualHigherSZeroPhysicalGraph.nativeZeroHalf ActualSFirstPhysicalDictionary.nativeAdjointZeroHalf
  ActualHigherSFormation.higherSInput ActualHigherSQuadraticZeroQuartic.actualZ2Half
  ActualHigherSQuadraticZeroQuartic.actualT2Half ActualHigherSLinearZero.linearZeroHigh
  ActualHigherSLinearZero.linearAdjointZeroHigh genuineReferenceZeroReverseHalf
  nativeReferenceZeroCoefficient nativeReferenceAdjointZeroCoefficient sphereSobolevHalfToSphereL2L

private lemma decode_original_half (G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x)=G.val x := by
  have h := halfToSphereL2_finiteCoreLift hO hD G x
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift] at h
  exact h

/-- The physical core-valued T zero coefficients are exactly the inherited Half lifts. -/
theorem original_zero_half_decodes (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (T0 q dr Ar p hdr hAr F x)=
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x ∧
    KL (Td0 q dr Ar p hdr hAr F x)=
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F).val x := by
  constructor
  · simpa only [rawForwardZeroHalf] using decode_original_half hO hD
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x
  · simpa only [rawAdjointZeroHalf] using decode_original_half hO hD
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x

/-- Intermediate algebra only; the final producer internally supplies both dictionary equalities. -/
theorem original_density_eq_three_pieces (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hForward : KL (S0 g2 dr Ar p hdr hAr q F x)=
      KL (Z2 g2 dr Ar p q F x)+KL (Z1 g2 dr Ar p q x (UF F x)))
    (hReverse : KL (Sd0 g2 dr Ar p hdr hAr q F x)=
      KL (T2 g2 dr Ar p q F x)+KL (T1 g2 dr Ar p q x (UF F x))) :
    D00 g2 dr Ar p hdr hAr q F x=
      GD g2 dr Ar p hdr hAr q F x+CD g2 dr Ar p hdr hAr q F x+
        LD g2 dr Ar p hdr hAr q F x := by
  have hDecode := original_zero_half_decodes hF hO hD g L hg dr Ar p hdr hAr q F x
  have hAlg := three_piece_identity (KL (T0 q dr Ar p hdr hAr F x))
    (KL (Td0 q dr Ar p hdr hAr F x)) (KL (RHalf q dr Ar p F x))
    (KL (Z2 g2 dr Ar p q F x)) (KL (T2 g2 dr Ar p q F x))
    (KL (Z1 g2 dr Ar p q x (UF F x))) (KL (T1 g2 dr Ar p q x (UF F x)))
    (KL (S0 g2 dr Ar p hdr hAr q F x)) (KL (Sd0 g2 dr Ar p hdr hAr q F x))
    hForward hReverse
  calc
    _ = 4*(⟪KL (T0 q dr Ar p hdr hAr F x),KL (S0 g2 dr Ar p hdr hAr q F x)⟫_ℝ-
        ⟪KL (Td0 q dr Ar p hdr hAr F x),KL (Sd0 g2 dr Ar p hdr hAr q F x)⟫_ℝ) := by
      unfold originalZeroZeroCrossDensity
      rw [hDecode.1,hDecode.2]
    _ = _ := by
      simpa only [genuineQuadraticZeroCrossDensity,negativeCorrectionQuadraticDensity,
        signedLinearZeroCrossDensity,rawForwardZeroHalf,map_sub] using hAlg

/-- Literal original signed zero/zero T/S bound, with every analytic premise internally closed. -/
theorem exists_original_zero_zero_pointwise_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Czero etaZero : ℝ, 0 < Czero ∧ 0 < etaZero ∧ etaZero ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaZero →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ x ∈ tsupport F.val,
      |D00 g2 dr Ar p hdr hAr q F x| ≤ Czero*eta*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨CQ,eQ,hCQ,heQ,heQ0,hQ⟩ := exists_original_genuine_quadratic_zero_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨CC,eC,hCC,heC,heC0,hCorrection⟩ := exists_original_correction_quadratic_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨CL,eL,hCL,heL,heL0,hLinear⟩ := exists_original_signed_linear_zero_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL g2 hg2
  obtain ⟨eD,heD,heD0,hDictionary⟩ := exists_original_zero_physical_word_dictionary
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  let Czero := CQ+CC+CL
  let etaZero := min eD (min eQ (min eC eL))
  refine ⟨Czero,etaZero,by dsimp only [Czero]; positivity,
    lt_min heD (lt_min heQ (lt_min heC heL)),(min_le_left _ _).trans heD0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs x hx
  have hED : eta ≤ eD := he.trans (min_le_left _ _)
  have hEQ : eta ≤ eQ := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hEC : eta ≤ eC := he.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hEL : eta ≤ eL := he.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hZeroDict := hDictionary q hq dr hdr hdr1 Ar hAr p hp eta heta hED K hK hKball F hsupp hb hs x
  have hIdentity := original_density_eq_three_pieces
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    g2 dr Ar p hdr hAr q F x hZeroDict.1 hZeroDict.2
  have hQB := hQ q hq dr hdr hdr1 Ar hAr p hp eta heta hEQ K hK hKball F hsupp hb hs x hx
  have hCB := hCorrection q hq dr hdr hdr1 Ar hAr p hp eta heta hEC K hK hKball F hsupp hb hs x hx
  have hLB := hLinear q hq dr hdr hdr1 Ar hAr p hp eta heta hEL K hK hKball F hsupp hb hs x hx
  calc
    _ = |GD g2 dr Ar p hdr hAr q F x+CD g2 dr Ar p hdr hAr q F x+
        LD g2 dr Ar p hdr hAr q F x| := congrArg abs hIdentity
    _ ≤ |GD g2 dr Ar p hdr hAr q F x|+|CD g2 dr Ar p hdr hAr q F x|+
        |LD g2 dr Ar p hdr hAr q F x| :=
      by
        have hA := norm_add_le (GD g2 dr Ar p hdr hAr q F x)
          (CD g2 dr Ar p hdr hAr q F x)
        have hB := norm_add_le (GD g2 dr Ar p hdr hAr q F x+CD g2 dr Ar p hdr hAr q F x)
          (LD g2 dr Ar p hdr hAr q F x)
        have hTotal := hB.trans (add_le_add hA
          (le_refl ‖LD g2 dr Ar p hdr hAr q F x‖))
        simpa only [Real.norm_eq_abs] using hTotal
    _ ≤ CQ*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q dr Ar p x) F x+
        CC*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q dr Ar p x) F x+
        CL*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q dr Ar p x) F x :=
      add_le_add (add_le_add hQB hCB) hLB
    _ = _ := by dsimp only [Czero]; ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralPointwise
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroLiteralPointwise.exists_original_zero_zero_pointwise_bound
