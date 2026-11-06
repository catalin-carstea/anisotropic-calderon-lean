import Calderon.ActualHigherSAdjointFormation
import Calderon.ActualTSPrincipalAngularCaps
import Calderon.FixedParameterProfileBudgets

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseEOrdinaryCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualFiniteHarmonicCore ActualHigherSFormation ActualGeneratorEPairedGainedEndpoints
  ActualReverseEHigherLift ActualCommonFirstWordQuadraticAdjoint FixedParameterProfilePullback
  FixedParameterProfileBudgets ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth
  ActualHigherSCoordinateWeightBounds ActualHigherSLeadingBracketGain ActualScalarPrincipalAdjoint

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace

/-- Explicit conclusions supplied by the genuine physical cap producer. -/
def PhysicalFirstCaps {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : ℝ) (f : Tpar → V) (M KT dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) : Prop :=
  ContDiffAt ℝ ∞ (fun y => f (higherSParam L dr Ar p q y)) x ∧
    ‖f (higherSParam L dr Ar p q x)‖ ≤ M ∧
    ‖fderiv ℝ (fun y => f (higherSParam L dr Ar p q y)) x‖ ≤ M*KT

private lemma physical_first_caps {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : ℝ) (y0 : R3) (rho d M KT : ℝ) (f : Tpar → V) (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ ∞ f (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)))
    (hU : UniqueDiffOn ℝ (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)))
    (hcap : ∀ n : ℕ, n ≤ 1 → ∀ t ∈ Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1),
      ‖iteratedFDerivWithin ℝ n f (Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)) t‖ ≤ M)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (hT : ContDiffAt ℝ ∞ (higherSParam L dr Ar p q) x)
    (hmem : ∀ᶠ y in 𝓝 x, higherSParam L dr Ar p q y ∈
      Set.prod (commonRoom y0 rho d) (closedBall (0 : R3 →L[ℝ] ℝ) 1))
    (hTc : ‖fderiv ℝ (higherSParam L dr Ar p q) x‖ ≤ KT) :
    PhysicalFirstCaps L f M KT dr Ar p q x := by
  have hx := hmem.self_of_nhds
  have hc := physical_pullback_first_caps f (higherSParam L dr Ar p q) _ x
    (hf _ hx) hT hmem (hU _ hx) M (hcap 0 (by omega) _ hx) (hcap 1 (by omega) _ hx)
  exact ⟨hc.1,hc.2.1,hc.2.2.trans (mul_le_mul_of_nonneg_left hTc hM)⟩

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => higherSParam L dr Ar p q
attribute [local irreducible] reverseEHigh reverseELow

/-- One actual ordinary reverse-E cap packet on the caller's unchanged radius. -/
structure ReverseEOrdinaryPhysicalCaps (δ : ℝ) where
  M : ℝ
  M_nonneg : 0 ≤ M
  KT : ℝ
  KT_pos : 0 < KT
  eta0 : ℝ
  eta0_pos : 0 < eta0
  eta0_le : eta0 ≤ 1
  smooth : ∀ j : Fin 3,
    ContDiffOn ℝ ∞ (eH j) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (eL j) (ParamRoom δ)
  joint_caps : ∀ j : Fin 3, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom δ,
    ‖iteratedFDerivWithin ℝ n (eH j) (ParamRoom δ) t‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (eL j) (ParamRoom δ) t‖ ≤ M
  physical_caps : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ eta0 →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    (∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom δ) ∧
      ∀ j : Fin 3, PhysicalFirstCaps L (eH j) M KT dr Ar p q x ∧
        PhysicalFirstCaps L (eL j) M KT dr Ar p q x

/-- All caps are produced from the original actual germs on exactly the retained W room. -/
theorem exists_reverseEOrdinaryPhysicalCaps (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    Nonempty (ReverseEOrdinaryPhysicalCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ) := by
  classical
  have hK : IsCompact (ParamRoom δ) := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 Cm.rev.pos).prod
      (uniqueDiffOn_convex (convex_closedBall _ _) ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have hSH (j : Fin 3) : ContDiffOn ℝ ∞ (eH j) (ParamRoom δ) :=
    fun t ht => (Cm.rev.germHigh j t ht).contDiffWithinAt
  have hSL (j : Fin 3) : ContDiffOn ℝ ∞ (eL j) (ParamRoom δ) :=
    fun t ht => (Cm.rev.germLow j t ht).contDiffWithinAt
  choose CH hCH using fun j : Fin 3 =>
    exists_compact_iteratedFDerivWithin_bound (eH j) (ParamRoom δ) hK hU (hSH j) 1
  choose CL hCL using fun j : Fin 3 =>
    exists_compact_iteratedFDerivWithin_bound (eL j) (ParamRoom δ) hK hU (hSL j) 1
  let M : ℝ := ∑ j : Fin 3, (CH j+CL j)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ => add_nonneg (hCH j).1 (hCL j).1)
  have hCaps (j : Fin 3) (n : ℕ) (hn : n ≤ 1) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ‖iteratedFDerivWithin ℝ n (eH j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (eL j) (ParamRoom δ) t‖ ≤ M := by
    have hj : CH j+CL j ≤ M := Finset.single_le_sum
      (fun k _ => add_nonneg (hCH k).1 (hCL k).1) (Finset.mem_univ j)
    have hCH0 := (hCH j).1
    have hCL0 := (hCL j).1
    exact ⟨((hCH j).2 n hn t ht).trans (by linarith),
      ((hCL j).2 n hn t ht).trans (by linarith)⟩
  obtain ⟨KT,hKT,hTcap⟩ := exists_uniform_higherSParam_derivative_bound g hg L hL
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨eta0,he0,he1,hguard⟩ := exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δ Cm.rev.pos
    (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨{
    M := M
    M_nonneg := hM
    KT := KT
    KT_pos := hKT
    eta0 := eta0
    eta0_pos := he0
    eta0_le := he1
    smooth := fun j => ⟨hSH j,hSL j⟩
    joint_caps := hCaps
    physical_caps := ?_
  }⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs
  have hGuard := hguard q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hx hxBall hb hs
  have hmem := higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x hGuard
  have hT : ContDiffAt ℝ ∞ (Tq dr Ar p q) x :=
    (contDiff_radiusProfileMap q (referenceRadius dr Ar p L)
      (contDiff_referenceRadius_actual dr Ar p L hdr hAr)).contDiffAt
  have hTc := hTcap q hq dr hdr hdr1 Ar hAr p hp eta heta (heta0.trans he1) x hx hb hs
  refine ⟨hmem,?_⟩
  intro j
  exact ⟨physical_first_caps L y0 ρ δ M KT (eH j) hM (hSH j) hU
    (fun n hn t ht => (hCaps j n hn t ht).1) dr Ar p q x hT hmem hTc,
    physical_first_caps L y0 ρ δ M KT (eL j) hM (hSL j) hU
    (fun n hn t ht => (hCaps j n hn t ht).2) dr Ar p q x hT hmem hTc⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualReverseEOrdinaryCaps
