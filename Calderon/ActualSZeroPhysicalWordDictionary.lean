import Calderon.ActualSFirstPhysicalDictionary
import Calderon.ActualLowerSSelfPhysicalDecomposition

/-! Exact original S-zero physical dictionary.
Before-code: ../S-zero-physical-dictionary-before-source-nov03-night-v001/.
This is retained T/S interface matching; no new S-self or coercivity proof.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSZeroPhysicalWordDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualSFirstPhysicalDictionary ReferenceWeightedApproximation ReferenceDensityBounds
  ConformalDepth ActualHigherSLeadingBracketGain

private lemma reverse_first_contraction {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℝ) (c : Fin 3 → Fin 3 → ℝ) (A : Fin 3 → E →L[ℝ] V) (u : Fin 3 → E) :
    (∑ k : Fin 3, ((-r^2) • (∑ j : Fin 3, c k j • A j)) (u k)) =
      -(r^2 • ∑ k : Fin 3, ∑ j : Fin 3, c k j • A j (u k)) := by
  simp only [_root_.smul_apply,_root_.sum_apply,_root_.neg_apply,
    neg_smul,Finset.smul_sum,Finset.sum_neg_distrib]

private lemma zero_output_of_full_split {V : Type*} [AddCommGroup V]
    {s p z q l : V} (hz : z=s-p) (hs : s=p+q+l) : z=q+l := by
  rw [hz,hs]
  abel

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
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "S0" => ActualHigherSZeroPhysicalGraph.nativeZeroHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
local notation "Sd0" => nativeAdjointZeroHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
local notation "SF" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "TF" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z2" => ActualHigherSQuadraticZeroQuartic.actualZ2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RS1" => referenceSAdjointFirstHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] ActualHigherSZeroPhysicalGraph.nativeZeroHalf
  nativeAdjointZeroHalf ActualHigherSFormation.nativeHigherSHalf
  ActualHigherSAdjointFormation.higherSAdjointHalf ActualHigherSFormation.nativeHigherSOut
  ActualHigherSAdjointFormation.higherSAdjointOut ActualHigherSFormation.higherSInput
  ActualPPLowerRemainder.actualPPFirstOut ActualPPLowerRemainder.actualPPReverseFirstOut
  sphereSobolevHalfToSphereL2L ActualHigherSQuadraticZeroQuartic.actualZ2Half
  ActualHigherSQuadraticZeroQuartic.actualT2Half
  ActualHigherSLinearZero.linearZeroHigh ActualHigherSLinearZero.linearAdjointZeroHigh
  ActualFullEGainedAssembly.orderedReverseHigh referenceSAdjointFirstHalf

/-- Literal original forward subtraction and exactly the same first coordinate action. -/
theorem original_forward_zero_output_eq_difference (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (S0 g2 dr Ar p hdr hAr q F x) =
      SF dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x-PF g2 dr Ar p q F x := by
  simp only [ActualHigherSZeroPhysicalGraph.nativeZeroHalf,map_sub,
    ActualHigherSFormation.nativeHigherSOut,ActualPPLowerRemainder.actualPPFirstOut,
    ActualHigherSFirstPhysicalCommutatorGraph.coordinateFirstAction]

/-- Exact ordered reverse first term, with its original negative sign. -/
theorem original_reverse_first_output_eq (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    PR g2 dr Ar p q F x=KL (RS1 g2 dr Ar p q (UF F) x) := by
  unfold ActualPPLowerRemainder.actualPPReverseFirstOut
  apply congrArg (fun v : Half => KL v)
  unfold ActualPPLowerRemainder.actualPPReverseFirstHigh
    orderedReverseFirstCoordinateFactorHigh referenceSAdjointFirstHalf
  exact reverse_first_contraction (referenceRadius dr Ar p L x)
    (fun k j => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x))
    (fun j => ActualFullEGainedAssembly.orderedReverseHigh
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j ((Tq dr Ar p q) x))
    (fun k => fderiv ℝ (UF F) x (coordinateDirection k))

/-- Exact original full adjoint subtraction; every original correction is retained. -/
theorem original_reverse_zero_output_eq_difference (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (Sd0 g2 dr Ar p hdr hAr q F x) =
      TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x-PR g2 dr Ar p q F x := by
  rw [original_reverse_first_output_eq hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0]
  simp only [nativeAdjointZeroHalf,map_sub,ActualHigherSAdjointFormation.higherSAdjointOut]

/-- Actual global physical dictionary on the original data, uniformly before all later inputs. -/
theorem exists_original_zero_physical_word_dictionary
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ etaDictionary : ℝ, 0 < etaDictionary ∧ etaDictionary ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaDictionary →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ x : R3,
      KL (S0 g2 dr Ar p hdr hAr q F x)=KL (Z2 g2 dr Ar p q F x)+KL (Z1 g2 dr Ar p q x (UF F x)) ∧
      KL (Sd0 g2 dr Ar p hdr hAr q F x)=KL (T2 g2 dr Ar p q F x)+KL (T1 g2 dr Ar p q x (UF F x)) := by
  obtain ⟨etaDictionary,hePos,he0,hSplit⟩ :=
    ActualLowerSSelfPhysicalDecomposition.exists_same_packet_physical_first_zero_split
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  refine ⟨etaDictionary,hePos,he0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs x
  have h := hSplit q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs x
  have hForward := original_forward_zero_output_eq_difference
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    g2 dr Ar p hdr hAr q F x
  have hReverse := original_reverse_zero_output_eq_difference
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    g2 dr Ar p hdr hAr q F x
  exact ⟨zero_output_of_full_split hForward h.1,
    zero_output_of_full_split hReverse h.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSZeroPhysicalWordDictionary
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSZeroPhysicalWordDictionary.exists_original_zero_physical_word_dictionary
