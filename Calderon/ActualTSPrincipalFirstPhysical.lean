import Calderon.ActualTFirstPhysicalDictionary
import Calderon.ActualSFirstPhysicalDictionary
import Calderon.ActualTSPrincipalCrossReference
import Calderon.ActualTSPrincipalPhysicalRegularity

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstPhysical

private lemma weighted_four_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : Fin 3 → Fin 3 → ℝ) (A C : Fin 3 → Fin 3 → E) (r : ℝ) :
    ⟪∑ l : Fin 3, ∑ i : Fin 3, a l i • A l i,
      r • (∑ k : Fin 3, ∑ j : Fin 3, b k j • C k j)⟫_ℝ =
    ∑ l : Fin 3, ∑ k : Fin 3, r*∑ i : Fin 3, ∑ j : Fin 3,
      (a l i*b k j)*⟪A l i,C k j⟫_ℝ := by
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma weighted_four_cross {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : Fin 3 → Fin 3 → ℝ) (A B C D : Fin 3 → Fin 3 → E) (r : ℝ) :
    ⟪∑ l : Fin 3, ∑ i : Fin 3, a l i • A l i,
      r • (∑ k : Fin 3, ∑ j : Fin 3, b k j • C k j)⟫_ℝ-
    ⟪-(∑ l : Fin 3, ∑ i : Fin 3, a l i • B l i),
      -(r • (∑ k : Fin 3, ∑ j : Fin 3, b k j • D k j))⟫_ℝ =
    ∑ l : Fin 3, ∑ k : Fin 3, r*∑ i : Fin 3, ∑ j : Fin 3,
      (a l i*b k j)*(⟪A l i,C k j⟫_ℝ-⟪B l i,D k j⟫_ℝ) := by
  simp only [inner_neg_left,inner_neg_right,neg_neg]
  rw [weighted_four_inner,weighted_four_inner]
  simp only [mul_sub,Finset.sum_sub_distrib]

private lemma integral_four (mu f : R3 → ℝ) :
    (∫ x, mu x*(4*f x))=4*(∫ x, mu x*f x) := by
  have he : (fun x => mu x*(4*f x))=(fun x => 4*(mu x*f x)) :=
    funext (fun x => by ring)
  rw [he,integral_const_mul]

open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualTFirstPhysicalDictionary ActualSFirstPhysicalDictionary ActualHigherSFormation
  ActualHigherSLeadingBracketGain ActualHigherSPhysicalPairing ActualTSPrincipalCrossReference
  ActualTSPrincipalPairingGraph ActualTSPrincipalPhysicalGreen ActualTSPrincipalAngularCaps
  ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorNativeForm
  ActualHigherSZeroScalarNativeForm ActualScalarPrincipalAdjoint
  ReferenceDensityBounds SmoothMetricFrame MovingFrameConnection ConformalDepth
  PrincipalCommutator ReferenceWeightedApproximation ActualTSPrincipalCoefficients
  ActualMixedAngularPairedGains FixedParameterProfilePullback FixedParameterProfileBudgets

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ordinary" => PrincipalOrdinaryRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "Tq" dr:max Ar:max p:max q:max => higherSParam L dr Ar p q
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "AH" => raisingHigh hF hO hD
local notation "aH" => loweringHigh hF hO hD
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => referenceFirstHalf hO hD hF g L
local notation "Td1" => referenceAdjointFirstHalf hO hD hF g L
local notation "S1" => referenceSFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sd1" => referenceSAdjointFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LC" => literalPrincipalFirstCross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PC" => principalCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  raisingHigh loweringHigh sphereSobolevInclusionL principalCoordinateCoefficient
  higherSInput

/-- Exactly the physical first/first contribution from the original T/S decomposition. -/
def firstPhysicalCross (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (U : R3 → Hi) (x : R3) : ℝ :=
  ⟪KL (T1 q U x),KL (S1 g2 dr Ar p q U x)⟫_ℝ-
    ⟪KL (Td1 q U x),KL (Sd1 g2 dr Ar p q U x)⟫_ℝ

local notation "FC" => firstPhysicalCross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

theorem first_physical_cross_eq_literal (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (q : ℝ) (U : R3 → Hi) (x : R3) :
    FC g2 dr Ar p q U x=∑ l : Fin 3, ∑ k : Fin 3, LC g2 dr Ar p q l k U x := by
  unfold firstPhysicalCross referenceFirstHalf referenceAdjointFirstHalf
    referenceSFirstHalf referenceSAdjointFirstHalf
  simp only [map_sum,map_smul,map_neg]
  have h := weighted_four_cross
    (fun l i => referenceMetricGramFrame g L (q,x) i l)
    (fun k j => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x))
    (fun l i => KL (AH i (fderiv ℝ U x (coordinateDirection l))))
    (fun l i => KL (aH i (fderiv ℝ U x (coordinateDirection l))))
    (fun k j => KL (EH j ((Tq dr Ar p q) x) (fderiv ℝ U x (coordinateDirection k))))
    (fun k j => KL (eH j ((Tq dr Ar p q) x) (fderiv ℝ U x (coordinateDirection k))))
    ((referenceRadius dr Ar p L x)^2)
  simp_rw [← halfPairing_eq_inner_sphereL2 hO hD] at h
  simpa only [literalPrincipalFirstCross,directionalFDeriv] using h

/-- Actual ordinary-room regularity and compact original input produce every integrability. -/
theorem integrable_literal_principal_first_cross (ordinary : Ordinary)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom ordinary.δ)
    (l k : Fin 3) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      LC g2 dr Ar p q l k (higherSInput hO hD F) x) := by
  let K : Set R3 := tsupport F.val
  let U := higherSInput hO hD F
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let v : R3 → Half := fun x => PC g2 dr Ar p q l k x
    (directionalFDeriv (coordinateDirection k) U x)
  have hK : IsCompact K := F.property.2.1
  have hU : ContDiff ℝ ∞ U := by
    simpa only [U,higherSInput] using contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have h0 : ∀ x ∉ K, U x=0 := highInput_eq_zero_off hO hD F
  have hD0 (j : Fin 3) (x : R3) (hx : x ∉ K) :
      directionalFDeriv (coordinateDirection j) U x=0 :=
    directional_eq_zero_off U K hK.isClosed h0 _ x hx
  have hA (x : R3) (hx : x ∈ K) :
      ContDiffAt ℝ ∞ (PC g2 dr Ar p q l k) x :=
    (principal_physical_coordinate_regular hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      ordinary g2 hg2 dr Ar p q hdr hAr x (hT x hx) l k).1
  have hv : ContDiff ℝ ∞ v := contDiff_supported_operator_apply
    (directionalFDeriv (coordinateDirection k) U) (PC g2 dr Ar p q l k) K hK.isClosed
    (contDiff_directionalFDeriv _ U hU) (hD0 k) hA
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  let f : R3 → ℝ := fun x => mu x*highDualPairingL
    (directionalFDeriv (coordinateDirection l) U x) (v x)
  have hf : Continuous f := hm.continuous.mul
    ((continuous_const.clm_apply (contDiff_directionalFDeriv _ U hU).continuous).clm_apply hv.continuous)
  have hfc : HasCompactSupport f := HasCompactSupport.intro hK (by
    intro x hx
    simp only [f,hD0 l x hx,map_zero,ContinuousLinearMap.zero_apply,mul_zero])
  have hi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have he : (fun x => mu x*LC g2 dr Ar p q l k U x)=f := by
    funext x
    exact congrArg (fun z : ℝ => mu x*z)
      (coordinate_first_pairing_eq_principal hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
        g2 dr Ar p q l k x (directionalFDeriv (coordinateDirection l) U x)
        (directionalFDeriv (coordinateDirection k) U x)).symm
  rw [he]
  exact hi

/-- Integration genuinely distributes over all nine original physical coordinate terms. -/
theorem integral_first_physical_cross_eq_coordinate_sum (ordinary : Ordinary)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom ordinary.δ) :
    (∫ x, referenceDensityFamily g L (q,x)*FC g2 dr Ar p q (higherSInput hO hD F) x) =
      ∑ l : Fin 3, ∑ k : Fin 3,
        ∫ x, referenceDensityFamily g L (q,x)*LC g2 dr Ar p q l k (higherSInput hO hD F) x := by
  let f : Fin 3 → Fin 3 → R3 → ℝ := fun l k x =>
    referenceDensityFamily g L (q,x)*LC g2 dr Ar p q l k (higherSInput hO hD F) x
  have hi (l k : Fin 3) : Integrable (f l k) :=
    integrable_literal_principal_first_cross hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      ordinary g2 hg2 dr Ar p hdr hAr q F hT l k
  have he : (fun x => referenceDensityFamily g L (q,x)*FC g2 dr Ar p q (higherSInput hO hD F) x) =
      (fun x => ∑ l : Fin 3, ∑ k : Fin 3, f l k x) := by
    funext x
    rw [first_physical_cross_eq_literal hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg]
    simp only [Finset.mul_sum,f]
  rw [he,integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun k _ => hi l k))]
  apply Finset.sum_congr rfl
  intro l _
  exact integral_finsetSum _ (fun k _ => hi l k)

/-- Original signed factor4 principal T/S physical integral, with all helper premises discharged.
The constant is chosen AFTER the fixed g2, so it is not uniform over a metric neighborhood. -/
theorem exists_first_physical_cross_reference_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (d0 : ℝ) (germs : CoeffRoom d0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg d0 germs) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ data.eta0 ∧
      ∀ g2 : MatrixField, ∀ hg2 : IsAdmissibleMetric g2, ∃ Bc : ℝ, 0 < Bc ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ ball y0 ρ →
      (∀ x ∈ tsupport F.val, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ tsupport F.val, referenceRadius dr Ar p L x*
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      |∫ x, referenceDensityFamily g L (q,x)*(4*FC g2 dr Ar p q (higherSInput hO hD F) x)| ≤
        Bc*eta*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨etaA,hA,hAle,hBound⟩ := exists_literal_principal_coordinate_sum_reference_bound
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hL hreg d0 germs data
  let ordinary := Classical.choice (exists_principalOrdinaryRoom
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg)
  let guardWitness := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ ordinary.δ
    ordinary.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaRoom : ℝ := Classical.choose guardWitness
  have roomFacts := Classical.choose_spec guardWitness
  refine ⟨min etaA etaRoom,lt_min hA roomFacts.1,(min_le_left _ _).trans hAle,?_⟩
  intro g2 hg2
  obtain ⟨Bc,hBc,hRows⟩ := hBound g2 hg2
  refine ⟨4*Bc,mul_pos (by norm_num) hBc,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 F hsupp hb hs
  have hetaA : eta ≤ etaA := heta0.trans (min_le_left _ _)
  have hetaRoom : eta ≤ etaRoom := heta0.trans (min_le_right _ _)
  have hT (x : R3) (hx : x ∈ tsupport F.val) :
      (Tq dr Ar p q) x ∈ ParamRoom ordinary.δ := by
    have ht := roomFacts.2.2 q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom x
      (ball_subset_closedBall (hsupp hx)) (hsupp hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ ordinary.δ L dr Ar q p hdr hAr x ht).self_of_nhds
  have he := integral_first_physical_cross_eq_coordinate_sum
    hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    ordinary g2 hg2 dr Ar p hdr hAr q F hT
  have hRow := hRows q hq dr hdr hdr1 Ar hAr p hp eta heta hetaA F hsupp hb hs
  rw [integral_four,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<4),he]
  calc
    _ ≤ 4*(Bc*eta*∫ x, referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) :=
        mul_le_mul_of_nonneg_left hRow (by norm_num)
    _ = (4*Bc)*eta*∫ x, referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by ring


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstPhysical

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstPhysical.first_physical_cross_eq_literal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstPhysical.integrable_literal_principal_first_cross
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstPhysical.integral_first_physical_cross_eq_coordinate_sum

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalFirstPhysical.exists_first_physical_cross_reference_bound
