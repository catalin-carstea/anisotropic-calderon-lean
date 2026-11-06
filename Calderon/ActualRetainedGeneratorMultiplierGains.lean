import Calderon.ActualPiJacobiRadialGainedRows

/-! Source-only Sol author prerequisite. Full upfront:
generator-multiplier-before-v001. Actual current Pi/nine-Jacobi witnesses are
retained; degree B has eigenvalue k, including zero. Not the full W/E result. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualRetainedGeneratorMultiplierGains
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

abbrev Generator := (Fin 3 × Fin 3) ⊕ Unit
abbrev RetainedCoefficient := (Fin 3) ⊕ (Fin 3 × Fin 3)

def generatorHigh : Generator → Hi →L[ℝ] Half
  | Sum.inl ij => sphereSobolevRotationL (3/2 : ℝ) ij.1 ij.2
  | Sum.inr _ => sphereSobolevShiftedDegreeL (3/2 : ℝ)
def generatorLow : Generator → Half →L[ℝ] Neg
  | Sum.inl ij => sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2
  | Sum.inr _ => sphereSobolevShiftedDegreeL (1/2 : ℝ)

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

/-- Keep each original coefficient parameter space: Pi uses t, Jacobi uses p=t.1. -/
def retainedJets (δ0 : ℝ) (W : CoeffRoom δ0) : RetainedCoefficient → Tpar → SmoothCoefficientJets 3
  | Sum.inl i, t => piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i t
  | Sum.inr im, t => jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W im.1 im.2 t.1

/-- Two separately constructed actual order-zero endpoint gains. -/
def generatorMultiplierGains (V : Generator) (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) :
    (Hi →L[ℝ] Hi) × (Half →L[ℝ] Half) :=
  match V with
  | Sum.inl ij => (NH (rotationJets Q ij.1 ij.2),NL (smoothMultiplierLowerJets (rotationJets Q ij.1 ij.2)))
  | Sum.inr _ =>
    (rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg Q q y,
     rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData Q q y)
local notation "Gains" => generatorMultiplierGains g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def generatorMultiplierHigh (V : Generator) (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) : Hi →L[ℝ] Hi :=
  (Gains V Q q y).1
def generatorMultiplierHalf (V : Generator) (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) : Half →L[ℝ] Half :=
  (Gains V Q q y).2
local notation "UH" => generatorMultiplierHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "UL" => generatorMultiplierHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QW" => retainedJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def retainedGeneratorHigh (δ0 : ℝ) (W : CoeffRoom δ0) (V : Generator) (c : RetainedCoefficient) (t : Tpar) : Hi →L[ℝ] Hi :=
  UH V (QW δ0 W c t) t.1.1 t.1.2.1
def retainedGeneratorHalf (δ0 : ℝ) (W : CoeffRoom δ0) (V : Generator) (c : RetainedCoefficient) (t : Tpar) : Half →L[ℝ] Half :=
  UL V (QW δ0 W c t) t.1.1 t.1.2.1
local notation "GH" => retainedGeneratorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GL" => retainedGeneratorHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

private lemma actual_generator_multiplier_graphs
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (lam Lam : ℝ) (V : Generator) (Q : SmoothCoefficientJets 3) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : y ∈ closedBall y0 ρ) (hG : Guard lam Lam (q,(y,0))) :
    (∀ u : Hi, IH (UH V Q q y u)=generatorHigh V (NH Q u)-NL (smoothMultiplierLowerJets Q) (generatorHigh V u)) ∧
    (∀ v : Half, JL (UL V Q q y v)=generatorLow V (NL (smoothMultiplierLowerJets Q) v)-NN (smoothMultiplierLowerJets Q) (generatorLow V v)) := by
  cases V with
  | inl ij =>
    refine ⟨fun u => ?_,fun v => ?_⟩
    · have h := rotation_high_product hcalc hF hO hD τ0 Q ij.1 ij.2 u
      exact (eq_sub_iff_add_eq).2 ((add_comm _ _).trans h.symm)
    · have h := rotation_half_product hcalc hF hO hD τ0 Q ij.1 ij.2 v
      exact (eq_sub_iff_add_eq).2 ((add_comm _ _).trans h.symm)
  | inr z =>
    exact ⟨degree_high_multiplier hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel lam Lam Q q hq y hy hG,
      degree_half_multiplier hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hKernel lam Lam Q q hq y hy hG⟩

/-- Actual public common-support topology applied to one original parameter space. -/
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

/-- ALL current original Pi/Jacobi coefficient generator gains, at both actual
order-zero endpoints, jointly smooth and with all finite joint caps on ONE room.
The two graph levels are proved separately; no low cap is inferred from high. -/
private def retainedGeneratorMultiplierFoldedContract (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      (∀ V : Generator, ∀ c : RetainedCoefficient,
        ContDiffOn ℝ ∞ (GH δ0 W V c) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (GL δ0 W V c) (ParamRoom δ)) ∧
      (∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        (∀ u : Hi, IH (GH δ0 W V c t u)=generatorHigh V (NH (QW δ0 W c t) u)-
          NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V u)) ∧
        (∀ v : Half, JL (GL δ0 W V c t v)=generatorLow V (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v)-
          NN (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorLow V v))) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ n : ℕ, n ≤ N →
        ∀ t ∈ ParamRoom δ,
          ‖iteratedFDerivWithin ℝ n (GH δ0 W V c) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (GL δ0 W V c) (ParamRoom δ) t‖ ≤ M)
attribute [local irreducible] retainedGeneratorMultiplierFoldedContract

private theorem retainedGeneratorMultiplierFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    retainedGeneratorMultiplierFoldedContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W := by
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
  have hSm (V : Generator) (c : RetainedCoefficient) :
      ContDiffOn ℝ ∞ (GH δ0 W V c) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (GL δ0 W V c) (ParamRoom δ) :=
    ⟨fun t ht => (hAt V c t ht).1.contDiffWithinAt,fun t ht => (hAt V c t ht).2.contDiffWithinAt⟩
  have hK : IsCompact (ParamRoom δ) := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  unfold retainedGeneratorMultiplierFoldedContract
  refine ⟨δ,hδ,min_le_left _ _,(min_le_right _ _).trans hdFρ,hSm,?_,?_⟩
  · intro V c t ht
    exact actual_generator_multiplier_graphs g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel lam Lam V (QW δ0 W c t) t.1.1 ht.1.1 t.1.2.1 ht.1.2.1 (hG0 t.1 ht.1)
  · intro N
    choose MH hMH using fun z : Generator × RetainedCoefficient =>
      exists_compact_iteratedFDerivWithin_bound (GH δ0 W z.1 z.2) (ParamRoom δ) hK hU (hSm z.1 z.2).1 N
    choose ML hML using fun z : Generator × RetainedCoefficient =>
      exists_compact_iteratedFDerivWithin_bound (GL δ0 W z.1 z.2) (ParamRoom δ) hK hU (hSm z.1 z.2).2 N
    let M := ∑ z : Generator × RetainedCoefficient, (MH z+ML z)
    have hM0 : 0 ≤ M := Finset.sum_nonneg (fun z _ => add_nonneg (hMH z).1 (hML z).1)
    refine ⟨M,hM0,?_⟩
    intro V c n hn t ht
    have hOne : MH (V,c)+ML (V,c) ≤ M :=
      Finset.single_le_sum (fun z _ => add_nonneg (hMH z).1 (hML z).1) (Finset.mem_univ (V,c))
    have hH := (hMH (V,c)).2 n hn t ht
    have hL := (hML (V,c)).2 n hn t ht
    have hH0 := (hMH (V,c)).1
    have hL0 := (hML (V,c)).1
    exact ⟨hH.trans (by linarith),hL.trans (by linarith)⟩


theorem exists_commonRoom_retained_generator_multiplier_gains
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      (∀ V : Generator, ∀ c : RetainedCoefficient,
        ContDiffOn ℝ ∞ (GH δ0 W V c) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (GL δ0 W V c) (ParamRoom δ)) ∧
      (∀ V : Generator, ∀ c : RetainedCoefficient, ∀ t ∈ ParamRoom δ,
        (∀ u : Hi, IH (GH δ0 W V c t u)=generatorHigh V (NH (QW δ0 W c t) u)-
          NL (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorHigh V u)) ∧
        (∀ v : Half, JL (GL δ0 W V c t v)=generatorLow V (NL (smoothMultiplierLowerJets (QW δ0 W c t)) v)-
          NN (smoothMultiplierLowerJets (QW δ0 W c t)) (generatorLow V v))) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ V : Generator, ∀ c : RetainedCoefficient, ∀ n : ℕ, n ≤ N →
        ∀ t ∈ ParamRoom δ,
          ‖iteratedFDerivWithin ℝ n (GH δ0 W V c) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (GL δ0 W V c) (ParamRoom δ) t‖ ≤ M) := by
  simpa only [retainedGeneratorMultiplierFoldedContract] using
    (retainedGeneratorMultiplierFoldedContract_proof g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualRetainedGeneratorMultiplierGains
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualRetainedGeneratorMultiplierGains.exists_commonRoom_retained_generator_multiplier_gains
