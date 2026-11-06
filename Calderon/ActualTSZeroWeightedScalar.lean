import Calderon.ActualTSZeroWordPairing
import Calderon.ActualReferenceZeroECommutators
import Calderon.ActualHigherSLinearZeroScalarCaps
import Calderon.ActualHigherSZeroWordCoefficientBound
import Calderon.ActualHigherSZeroWordLiteralDictionary
import Calderon.ActualLowerSSelfFormation

/-!
Before-code: ../T-S-L00-weighted-assembly-before-source-nov03-night-v001/.
The exact signed coefficient-weighted T30/S207 scalar is bounded on original
input support. Its physical native T0/S0 dictionary and remaining correction/
linear terms are separate required work; no literal L00 completion is claimed.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroWeightedScalar
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualHigherSZeroCoefficientBounds ActualAllAngularAtomGainedRoom
  ActualTSZeroWordPairing ActualReferenceZeroECommutators ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroWords ReferenceWeightedApproximation ReferenceDensityBounds
  ConformalDepth AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection

private lemma abs_mixed_word_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ) (R : ι → κ → ℝ) (A B D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hc : ∀ i, |c i| ≤ A) (hd : ∀ j, |d j| ≤ B) (hR : ∀ i j, |R i j| ≤ D) :
    |∑ i : ι, ∑ j : κ, (c i*d j)*R i j| ≤
      (Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)*A*B*D := by
  have hrow (i : ι) (j : κ) : |(c i*d j)*R i j| ≤ A*B*D := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hc i) (hd j) (abs_nonneg _) hA) (hR i j)
      (abs_nonneg _) (mul_nonneg hA hB)
  calc
    _ ≤ ∑ i : ι, |∑ j : κ, (c i*d j)*R i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, ∑ j : κ, |(c i*d j)*R i j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : κ, A*B*D :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hrow i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

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


local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "cc" => referenceAngularZeroCoefficient g L
local notation "WC" => actualWordCoefficient g L
local notation "DPair" => actualOrderedWordPairingDefect
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
local notation "PN" => ActualHigherSPairingNormDiagnostic.standardPairingNorm PL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Literal signed factor4, thirty T words and all207 S words, both Q orders. -/
def signedWeightedQuadraticZero (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*∑ i : Fin 3, ∑ V : Generator, ∑ z : ZeroWord,
    (cc q dr Ar p x i V*WC g2 dr Ar p q x z)*
      DPair dr Ar p q F x (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl V))
        (wordAtoms z).1 (wordAtoms z).2
local notation "W00" => signedWeightedQuadraticZero
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

private lemma reference_log_frame_eq_radius_horizontal
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (i : Fin 3) :
    referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x =
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i := by
  unfold referenceRadiusHorizontalLogDerivative
  rw [conformalFrame_coordinateVector_eq g L q x i]
  rfl

attribute [local irreducible] ActualHigherSFormation.higherSInput
  actualOrderedWordPairingDefect signedWeightedQuadraticZero

/-- Actual coefficient and finite-input word bounds close all premises internally.
This is the selected weighted scalar, before its exact native physical dictionary. -/
theorem exists_original_weighted_zero_quadratic_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cquad etaQuad : ℝ, 0 < Cquad ∧ 0 < etaQuad ∧ etaQuad ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaQuad →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ x ∈ tsupport F.val,
      |W00 g2 dr Ar p q F x| ≤ Cquad*eta*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨Mop,etaWord,hMop,hetaWord,_hetaWord0,hWord⟩ :=
    exists_original_finite_input_word_pair_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel
  obtain ⟨Msc,hMsc,hScalars⟩ :=
    ActualHigherSLinearZeroScalarCaps.exists_word_scalar_caps g hg L hL y0 ρ g2 hg2
  let D : ℝ := 4*30*207*Msc^3*(4*PN*Mop^3)
  let Cquad : ℝ := 1+D
  let etaQuad : ℝ := min data.eta0 (min 1 etaWord)
  have hPN : 0 ≤ PN := ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  have hMop0 : 0 ≤ Mop := zero_le_one.trans hMop
  have hMsc0 : 0 ≤ Msc := zero_le_one.trans hMsc
  have hDbudget : 0 ≤ D := by dsimp only [D]; positivity
  have hCquad : 0 < Cquad := by dsimp only [Cquad]; linarith only [hDbudget]
  refine ⟨Cquad,etaQuad,hCquad,lt_min data.eta0_pos (lt_min zero_lt_one hetaWord),
    min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaQuad K hK hKball F hsupp hb hs x hx
  have heWord : eta ≤ etaWord := hetaQuad.trans ((min_le_right _ _).trans (min_le_right _ _))
  have he1 : eta ≤ 1 := hetaQuad.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hxK := hsupp hx
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let U := UF F x
  let t := (Tq dr Ar p q) x
  have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hbX : 1 ≤ beta := hb x hxK
  have hb0 : 0 ≤ beta := zero_le_one.trans hbX
  have hsc := hScalars q hq dr hdr hdr1 Ar hAr p hp x
    (ball_subset_closedBall (hKball hxK)) hbX
  have hCoeffT (ia : Fin 3 × Generator) : |cc q dr Ar p x ia.1 ia.2| ≤ Msc*beta := by
    rcases ia with ⟨i,V⟩
    cases V with
    | inl ab =>
      simp only [referenceAngularZeroCoefficient,abs_mul,abs_div,abs_one,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ (1/2 : ℝ)*Msc := mul_le_mul_of_nonneg_left (hsc.2.1 i ab.1 ab.2) (by norm_num)
        _ ≤ Msc := by linarith only [hMsc0]
        _ ≤ Msc*beta := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hbX hMsc0
    | inr z =>
      simpa only [referenceAngularZeroCoefficient,
        reference_log_frame_eq_radius_horizontal g L q dr Ar p x i] using hsc.2.2.1 i
  have hGamma (i a b : Fin 3) :
      |ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b t| ≤ Msc := by
    simpa only [ActualHigherSZeroCoefficientFactorisation.parameterConnection_eq g hg L,
      ActualHigherSZeroCoefficientFactorisation.parameterGramFrame,
      ActualHigherSFormation.higherSParam,t] using hsc.2.1 i a b
  have hCoeffS (z : ZeroWord) : |WC g2 dr Ar p q x z| ≤ Msc^2*r :=
    ActualHigherSQuadraticZeroQuarticBounds.abs_wordCoefficient_le_common r beta Msc
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
      (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b t)
      hr hbX hMsc ((hs x hxK).trans he1) hsc.1 hsc.2.2.1 hGamma z
  let R : (Fin 3 × Generator) → ZeroWord → ℝ := fun ia z =>
    DPair dr Ar p q F x (Sum.inr (Sum.inr ia.1)) (Sum.inr (Sum.inl ia.2))
      (wordAtoms z).1 (wordAtoms z).2
  let Bop : ℝ := 4*PN*Mop^3*‖U‖^2
  have hBop : 0 ≤ Bop := by dsimp only [Bop]; positivity
  have hRows (ia : Fin 3 × Generator) (z : ZeroWord) : |R ia z| ≤ Bop :=
    hWord q hq dr hdr hdr1 Ar hAr p hp eta heta heWord K hK hKball F hsupp hb hs x hx
      (Sum.inr (Sum.inr ia.1)) (Sum.inr (Sum.inl ia.2)) (wordAtoms z).1 (wordAtoms z).2
  have hRaw := abs_mixed_word_sum_le
    (fun ia : Fin 3 × Generator => cc q dr Ar p x ia.1 ia.2)
    (WC g2 dr Ar p q x) R (Msc*beta) (Msc^2*r) Bop
    (mul_nonneg hMsc0 hb0) (mul_nonneg (sq_nonneg Msc) hr) hBop hCoeffT hCoeffS hRows
  have hCardT : Fintype.card (Fin 3 × Generator)=30 := by norm_num [Generator]
  rw [hCardT,card_zeroWord] at hRaw
  have hWeighted :
      |W00 g2 dr Ar p q F x| ≤ D*(r*beta)*‖U‖^2 := by
    have hExpand : W00 g2 dr Ar p q F x =
        4*∑ ia : Fin 3 × Generator, ∑ z : ZeroWord,
          (cc q dr Ar p x ia.1 ia.2*WC g2 dr Ar p q x z)*R ia z := by
      simp only [signedWeightedQuadraticZero,Fintype.sum_prod_type,R]
    rw [hExpand,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      _ ≤ 4*(30*207*(Msc*beta)*(Msc^2*r)*Bop) :=
        mul_le_mul_of_nonneg_left hRaw (by norm_num)
      _ = D*(r*beta)*‖U‖^2 := by dsimp only [D,Bop]; ring
  have hSmall : r*beta ≤ eta :=
    (mul_le_mul_of_nonneg_left (by nlinarith only [hbX] : beta ≤ beta^2) hr).trans (hs x hxK)
  have hEnergy := ActualLowerSSelfFormation.norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta hbX F x
  have hDC : D ≤ Cquad := by dsimp only [Cquad]; linarith
  calc
    _ ≤ D*(r*beta)*‖U‖^2 := hWeighted
    _ ≤ D*eta*‖U‖^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSmall hDbudget) (sq_nonneg _)
    _ ≤ Cquad*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hDC heta) hEnergy
        (sq_nonneg _) (mul_nonneg hCquad.le heta)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroWeightedScalar
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroWeightedScalar.exists_original_weighted_zero_quadratic_bound
