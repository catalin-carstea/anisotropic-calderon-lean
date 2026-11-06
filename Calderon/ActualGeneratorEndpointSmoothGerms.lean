import Calderon.ActualRetainedGeneratorMultiplierGains

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEndpointSmoothGerms
open ActualRetainedGeneratorMultiplierGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "Guard" => finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData

local notation "UH" => generatorMultiplierHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UL" => generatorMultiplierHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GL" => retainedGeneratorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private lemma commonSupport_generatorGains_contDiffAt
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → m (t,x)=0)
    (q : T → ℝ) (hq : ContDiff ℝ ∞ q) (y : T → R3) (hy : ContDiff ℝ ∞ y)
    (lam Lam : ℝ) (S : Set T) (hG0 : ∀ t ∈ S, Guard lam Lam (q t,(y t,0)))
    (V : Generator) (t : T) (ht : t ∈ S) :
    ContDiffAt ℝ ∞ (fun z => UH V (commonSupportCoefficientFamily 3 m hm K hK hz z) (q z) (y z)) t ∧
    ContDiffAt ℝ ∞ (fun z => UL V (commonSupportCoefficientFamily 3 m hm K hK hz z) (q z) (y z)) t := by
  cases V with
  | inl ij =>
    refine ⟨?_,?_⟩
    · exact (contDiff_nativeThreeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
        m hm K hK hz ij.1 ij.2).contDiffAt
    · exact (contDiff_nativeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
        m hm K hK hz ij.1 ij.2).contDiffAt
  | inr z =>
    refine ⟨?_,?_⟩
    · exact contDiffAt_rawAdjointMultiplierZero_commonSupport hcalc hF hO hD τ0
        g L y0 Φ B ε C ρ H a w hData hg m hm K hK hz q hq y hy t
        (by unfold referenceGaugeNormalHighInvertibleLocus; exact (hG0 t ht).2.2.2.1)
    · exact contDiffAt_rawHalfMultiplierZero_commonSupport hcalc hF hO hD τ0
        g L y0 Φ B ε C ρ H a w hData m hm K hK hz q hq y hy t
        (hG0 t ht).2.2.1.1 (hG0 t ht).2.2.1.2.1

/-- Neighborhood smoothness of the actual same-witness generator gains. -/
private def actualGeneratorEndpointGermsFoldedContract (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (GH δ0 W V c) t ∧ ContDiffAt ℝ ∞ (GL δ0 W V c) t
attribute [local irreducible] actualGeneratorEndpointGermsFoldedContract
private theorem actualGeneratorEndpointGermsFoldedContract_proof
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    actualGeneratorEndpointGermsFoldedContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W := by
  classical
  obtain ⟨lam,Lam,dF,_hlam,hdF,hdFρ,hFin⟩ := exists_finiteRoomGuard
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  let δ := min δ0 dF
  have hδ : 0 < δ := lt_min hδ0 hdF
  have hG0 (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) : Guard lam Lam (p.1,(p.2.1,0)) :=
    hFin _ ⟨hp.1,hp.2.1,⟨by linarith,by linarith⟩⟩
  have hAt (V : Generator) (c : RetainedCoefficient) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (GH δ0 W V c) t ∧ ContDiffAt ℝ ∞ (GL δ0 W V c) t := by
    cases c with
    | inl i =>
      exact commonSupport_generatorGains_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
        (fun z : Tpar => z.1.1) contDiff_fst.fst (fun z : Tpar => z.1.2.1) contDiff_fst.snd.fst
        lam Lam (ParamRoom δ) (fun z hz => hG0 z.1 hz.1) V t ht
    | inr im =>
      have h := commonSupport_generatorGains_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        (W.jacobiScalar im.1 im.2) (W.jacobiSmooth im.1 im.2) (W.jacobiSupport im.1 im.2)
        (W.jacobiCompact im.1 im.2) (W.jacobiZero im.1 im.2)
        (fun z : Pphys => z.1) contDiff_fst (fun z : Pphys => z.2.1) contDiff_snd.fst
        lam Lam (commonRoom y0 ρ δ) hG0 V t.1 ht.1
      exact ⟨h.1.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst,
        h.2.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst⟩
  unfold actualGeneratorEndpointGermsFoldedContract
  exact ⟨δ,hδ,min_le_left _ _,(min_le_right _ _).trans hdFρ,hAt⟩


theorem exists_commonRoom_retained_generator_multiplier_contDiffAt
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (GH δ0 W V c) t ∧ ContDiffAt ℝ ∞ (GL δ0 W V c) t := by
  simpa only [actualGeneratorEndpointGermsFoldedContract] using (actualGeneratorEndpointGermsFoldedContract_proof g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 hδ0 W)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEndpointSmoothGerms
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualGeneratorEndpointSmoothGerms.exists_commonRoom_retained_generator_multiplier_contDiffAt
