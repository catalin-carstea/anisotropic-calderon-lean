import Calderon.ActualTSZeroWeightedScalar
import Calderon.ActualTZeroWordRealization

/-!
Exact finite bilinear matching, all original coefficients and the signed factor4.
The native quadratic density uses genuine RHalf; the raw-adjoint correction and the
original S linear remainders of L00 are treated separately.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroPhysicalPairing
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualTSZeroWordPairing ActualTSZeroWeightedScalar
  ActualTZeroWordRealization ActualTZeroGenuineReverse ActualReferenceZeroECommutators
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualTZeroNegativeGraph ActualHigherSQuadraticZeroWords ReferenceWeightedApproximation
  ReferenceDensityBounds ConformalDepth AmbientReferenceRaising

private lemma inner_mixed_weighted_sums {Q ι κ : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (c : ι → ℝ) (d : κ → ℝ) (A : ι → Q) (X : κ → Q) :
    ⟪∑ i : ι, c i • A i,∑ j : κ, d j • X j⟫_ℝ =
      ∑ i : ι, ∑ j : κ, (c i*d j)*⟪A i,X j⟫_ℝ := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  simp only [real_inner_smul_left,inner_smul_right]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma mixed_weighted_pair_defect {Q ι κ : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (c : ι → ℝ) (d : κ → ℝ) (A B : ι → Q) (X Y : κ → Q) :
    ⟪∑ i : ι, c i • A i,∑ j : κ, d j • X j⟫_ℝ -
      ⟪∑ i : ι, c i • B i,∑ j : κ, d j • Y j⟫_ℝ =
      ∑ i : ι, ∑ j : κ, (c i*d j)*(⟪A i,X j⟫_ℝ-⟪B i,Y j⟫_ℝ) := by
  rw [inner_mixed_weighted_sums,inner_mixed_weighted_sums,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
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
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d


local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "cc" => referenceAngularZeroCoefficient g L
local notation "WC" => actualWordCoefficient g L
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "VA" => ActualHigherSQuadraticZeroQuartic.actualAtomHi
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => ActualHigherSQuadraticZeroQuartic.actualReverseAtomHi
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z2" => ActualHigherSQuadraticZeroQuartic.actualZ2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "FHalf" => referenceZeroForwardWordHalf
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "RHalf" => genuineReferenceZeroReverseHalf hF hO hD g L
local notation "DPair" => actualOrderedWordPairingDefect
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "W00" => signedWeightedQuadraticZero
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

def wordQuadraticZeroCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*(⟪KL (FHalf q dr Ar p F x),KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
    ⟪KL (RHalf q dr Ar p F x),KL (T2 g2 dr Ar p q F x)⟫_ℝ)
local notation "WD" => wordQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

/-- Actual original forward T-zero, genuine reverse quadratic partner, signed4. -/
def genuineQuadraticZeroCrossDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*(⟪KL (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x),
      KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
    ⟪KL (RHalf q dr Ar p F x),KL (T2 g2 dr Ar p q F x)⟫_ℝ)
local notation "GD" => genuineQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] angularAtomHigh angularAtomReverseHigh sphereSobolevHalfToSphereL2L
  ActualHigherSQuadraticZeroWords.atomHigh ActualHigherSQuadraticZeroWords.atomReverseHigh
  ActualHigherSQuadraticZeroQuartic.actualAtomHi ActualHigherSQuadraticZeroQuartic.actualReverseAtomHi
  ActualHigherSFormation.higherSInput actualOrderedWordPairingDefect signedWeightedQuadraticZero
  wordQuadraticZeroCrossDensity genuineQuadraticZeroCrossDensity referenceZeroForwardWordHalf

/-- All ordered coefficient pairs, with the original physical inner products. -/
theorem weighted_scalar_eq_word_pairing
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    W00 g2 dr Ar p q F x=WD g2 dr Ar p q F x := by
  let t := (Tq dr Ar p q) x
  let c : Fin 3 × Generator → ℝ := fun ia => cc q dr Ar p x ia.1 ia.2
  let d : ZeroWord → ℝ := WC g2 dr Ar p q x
  let A : Fin 3 × Generator → Half := fun ia =>
    AH t (Sum.inr (Sum.inr ia.1)) (VA dr Ar p q F x (Sum.inr (Sum.inl ia.2)))
  let BR : Fin 3 × Generator → Half := fun ia =>
    RH t (Sum.inr (Sum.inl ia.2)) (VB dr Ar p q F x (Sum.inr (Sum.inr ia.1)))
  let X : ZeroWord → Half := fun z => AH t (wordAtoms z).1 (VA dr Ar p q F x (wordAtoms z).2)
  let Y : ZeroWord → Half := fun z => RH t (wordAtoms z).2 (VB dr Ar p q F x (wordAtoms z).1)
  have hMixed := mixed_weighted_pair_defect (Q := SphereL2)
    (ι := Fin 3 × Generator) (κ := ZeroWord) c d
    (fun ia => KL (A ia)) (fun ia => KL (BR ia)) (fun z => KL (X z)) (fun z => KL (Y z))
  have hForward : FHalf q dr Ar p F x=∑ ia : Fin 3 × Generator, c ia • A ia := by
    have h := forward_half_eq_actual_word_sum
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data q dr Ar p F x
    simpa only [Fintype.sum_prod_type,c,A,t] using h
  have hR : RHalf q dr Ar p F x=∑ ia : Fin 3 × Generator, c ia • BR ia := by
    have h := genuine_reverse_half_eq_actual_word_sum
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data q dr Ar p F x
    simpa only [Fintype.sum_prod_type,c,BR,t] using h
  have hZ : Z2 g2 dr Ar p q F x=∑ z : ZeroWord, d z • X z := by
    have h := ActualHigherSQuadraticZeroQuartic.actualZ2Half_eq_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x
    refine h.trans ?_
    apply Finset.sum_congr rfl
    intro z _
    exact congrArg (fun K : Hi →L[ℝ] Half => d z • K (VA dr Ar p q F x (wordAtoms z).2))
      (ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (wordAtoms z).1)
  have hT : T2 g2 dr Ar p q F x=∑ z : ZeroWord, d z • Y z := by
    have h := ActualHigherSQuadraticZeroQuartic.actualT2Half_eq_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x
    refine h.trans ?_
    apply Finset.sum_congr rfl
    intro z _
    exact congrArg (fun K : Hi →L[ℝ] Half => d z • K (VB dr Ar p q F x (wordAtoms z).1))
      (ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (wordAtoms z).2)
  have hPair :
      ⟪KL (FHalf q dr Ar p F x),KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
        ⟪KL (RHalf q dr Ar p F x),KL (T2 g2 dr Ar p q F x)⟫_ℝ =
      ∑ ia : Fin 3 × Generator, ∑ z : ZeroWord, (c ia*d z)*
        DPair dr Ar p q F x (Sum.inr (Sum.inr ia.1)) (Sum.inr (Sum.inl ia.2))
          (wordAtoms z).1 (wordAtoms z).2 := by
    calc
      _ = ⟪KL (∑ ia, c ia • A ia),KL (∑ z, d z • X z)⟫_ℝ-
          ⟪KL (∑ ia, c ia • BR ia),KL (∑ z, d z • Y z)⟫_ℝ :=
        congrArg₂ (fun u v : ℝ => u-v)
          (congrArg₂ (fun u v : Half => ⟪KL u,KL v⟫_ℝ) hForward hZ)
          (congrArg₂ (fun u v : Half => ⟪KL u,KL v⟫_ℝ) hR hT)
      _ = ⟪∑ ia, c ia • KL (A ia),∑ z, d z • KL (X z)⟫_ℝ-
          ⟪∑ ia, c ia • KL (BR ia),∑ z, d z • KL (Y z)⟫_ℝ := by
        simp only [map_sum,map_smul]
      _ = ∑ ia, ∑ z, (c ia*d z)*(⟪KL (A ia),KL (X z)⟫_ℝ-⟪KL (BR ia),KL (Y z)⟫_ℝ) :=
        hMixed
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ia _
        apply Finset.sum_congr rfl
        intro z _
        unfold actualOrderedWordPairingDefect
        rfl
  have hSum : W00 g2 dr Ar p q F x=
      4*∑ ia : Fin 3 × Generator, ∑ z : ZeroWord, (c ia*d z)*
        DPair dr Ar p q F x (Sum.inr (Sum.inr ia.1)) (Sum.inr (Sum.inl ia.2))
          (wordAtoms z).1 (wordAtoms z).2 := by
    simp only [signedWeightedQuadraticZero,Fintype.sum_prod_type,c,d]
  unfold wordQuadraticZeroCrossDensity
  exact hSum.trans ((congrArg (fun r : ℝ => 4*r) hPair).symm)

/-- Exact original native forward field; no raw-adjoint correction is discarded. -/
theorem weighted_scalar_eq_genuine_native_pairing {radius : ℝ} (P : ARoom radius)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom radius) :
    W00 g2 dr Ar p q F x=GD g2 dr Ar p hdr hAr q F x := by
  have hBase := weighted_scalar_eq_word_pairing
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data g2 dr Ar p q F x
  have hN := native_zero_half_eq_forward_words
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    P q dr Ar p hdr hAr F x ht
  refine hBase.trans ?_
  unfold wordQuadraticZeroCrossDensity genuineQuadraticZeroCrossDensity
  exact congrArg (fun u : Half =>
    4*(⟪KL u,KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
      ⟪KL (RHalf q dr Ar p F x),KL (T2 g2 dr Ar p q F x)⟫_ℝ)) hN.symm

/-- Original physical quadratic density, uniform before all later profile inputs. -/
theorem exists_original_genuine_quadratic_zero_bound
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
      |GD g2 dr Ar p hdr hAr q F x| ≤ Cquad*eta*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨Cquad,etaWord,hC,heWord,heWord0,hBound⟩ :=
    exists_original_weighted_zero_quadratic_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨radius,hradius,_hrD,_hr0,_hrrho,_hInv,⟨P⟩⟩ :=
    ActualAllAngularAtomGainedRoom.exists_same_packet_allAngularAtom_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  let G := Classical.choice (ActualHigherSQuarticFactorization.exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL hKernel radius hradius)
  let etaQuad := min etaWord G.epsG
  refine ⟨Cquad,etaQuad,hC,lt_min heWord G.epsG_pos,(min_le_left _ _).trans heWord0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heQuad K hK hKball F hsupp hb hs x hx
  have hEW : eta ≤ etaWord := heQuad.trans (min_le_left _ _)
  have hEG : eta ≤ G.epsG := heQuad.trans (min_le_right _ _)
  have rooms := G.members q hq dr hdr hdr1 Ar hAr p hp eta heta hEG K hK hKball F hsupp hb hs
  have hEq := weighted_scalar_eq_genuine_native_pairing
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    P g2 dr Ar p hdr hAr q F x (rooms.1 x hx)
  exact (congrArg abs hEq).symm.le.trans
    (hBound q hq dr hdr hdr1 Ar hAr p hp eta heta hEW K hK hKball F hsupp hb hs x hx)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroPhysicalPairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroPhysicalPairing.weighted_scalar_eq_genuine_native_pairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroPhysicalPairing.exists_original_genuine_quadratic_zero_bound
