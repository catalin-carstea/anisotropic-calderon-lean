import Calderon.ActualLoweringEHighRoomAccess

/-! Small variable-high-room paired-low diagnostic owner. The copied generic
native4fact and finite-cap declarations are unchanged from Thin010. Read-only
Astra/high advice is advisory only; this implementation is routine Sol author
work, uncompiled and not independent review. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualCanonicalAngularGainedBracket ActualCanonicalGeneratorAngularGainedRows
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

attribute [local irreducible] sphereSobolevInclusionL v016TransposeL

/-- Exact checked four-fact result on opaque families; no projection or
existential destructuring is elaborated while instantiating the native API. -/
private theorem exists_smooth_paired_low_full
    (S : Set Tpar) (hS : UniqueDiffOn ℝ S)
    (Ch Dh : Tpar → Hi →L[ℝ] Half)
    (hCh : ContDiffOn ℝ ∞ Ch S) (hDh : ContDiffOn ℝ ∞ Dh S)
    (hAdj : ∀ t ∈ S, ∀ u v : Hi,
      PP (IH v) (JL (Ch t u)) = PP (IH u) (JL (Dh t v))) :
    ∃ Cl : Tpar → Half →L[ℝ] Neg,
      ContDiffOn ℝ ∞ Cl S ∧ ∀ t ∈ S,
        (Cl t).comp IH = (JL).comp (Ch t) ∧
        (I33).comp (Cl t) = (v016TransposeL (Dh t)).comp JL ∧
        ‖Cl t‖ ≤ (‖v016TransposeL (Dh t)‖+‖Ch t‖)/2 ∧
        ‖Cl t‖ ≤ (‖Dh t‖+‖Ch t‖)/2 :=
  v016_exists_contDiffOn_lowEndpoint S hS Ch Dh hCh hDh hAdj

/-- Finite-family smooth lows and all finite jet caps, with no actual packet
constructors in the balanced-family elaboration. All premises are discharged by
the original high room in the public producer. -/
private theorem exists_finite_smooth_paired_lows
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (Lf Rf : Fin 3 → Fin 3 → Tpar → Hi →L[ℝ] Half)
    (hLf : ∀ i j, ContDiffOn ℝ ∞ (Lf i j) S)
    (hRf : ∀ i j, ContDiffOn ℝ ∞ (Rf i j) S)
    (hAdj : ∀ i j t, t ∈ S → ∀ u v : Hi,
      PP (IH v) (JL (Lf i j t u)) = PP (IH u) (JL (Rf i j t v))) :
    ∃ Ll Rl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
      (∀ i j, ContDiffOn ℝ ∞ (Ll i j) S ∧ ContDiffOn ℝ ∞ (Rl i j) S) ∧
      (∀ i j t, t ∈ S →
        (Ll i j t).comp IH = (JL).comp (Lf i j t) ∧
        (Rl i j t).comp IH = (JL).comp (Rf i j t) ∧
        (I33).comp (Ll i j t) = (v016TransposeL (Rf i j t)).comp JL ∧
        (I33).comp (Rl i j t) = (v016TransposeL (Lf i j t)).comp JL ∧
        ‖Ll i j t‖ ≤ (‖Lf i j t‖+‖Rf i j t‖)/2 ∧
        ‖Rl i j t‖ ≤ (‖Lf i j t‖+‖Rf i j t‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ,
        n ≤ N → ∀ t ∈ S,
          ‖iteratedFDerivWithin ℝ n (Lf i j) S t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Rf i j) S t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Ll i j) S t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Rl i j) S t‖ ≤ M) := by
  classical
  have hLowL (i j : Fin 3) := exists_smooth_paired_low_full S hS
    (Lf i j) (Rf i j) (hLf i j) (hRf i j) (hAdj i j)
  have hSwap (i j : Fin 3) (t : Tpar) (ht : t ∈ S) (u v : Hi) :
      PP (IH v) (JL (Rf i j t u)) = PP (IH u) (JL (Lf i j t v)) :=
    (hAdj i j t ht v u).symm
  have hLowR (i j : Fin 3) := exists_smooth_paired_low_full S hS
    (Rf i j) (Lf i j) (hRf i j) (hLf i j) (hSwap i j)
  choose Ll hLl using hLowL
  choose Rl hRl using hLowR
  refine ⟨Ll,Rl,(fun i j => ⟨(hLl i j).1,(hRl i j).1⟩),?_,?_⟩
  · intro i j t ht
    exact ⟨((hLl i j).2 t ht).1,((hRl i j).2 t ht).1,
      ((hLl i j).2 t ht).2.1,((hRl i j).2 t ht).2.1,
      by simpa only [add_comm] using ((hLl i j).2 t ht).2.2.2,
      ((hRl i j).2 t ht).2.2.2⟩
  · intro N
    choose ML hML using fun z : Fin 3 × Fin 3 => exists_compact_iteratedFDerivWithin_bound
      (Lf z.1 z.2) S hK hS (hLf z.1 z.2) N
    choose MR hMR using fun z : Fin 3 × Fin 3 => exists_compact_iteratedFDerivWithin_bound
      (Rf z.1 z.2) S hK hS (hRf z.1 z.2) N
    choose MC hMC using fun z : Fin 3 × Fin 3 => exists_compact_iteratedFDerivWithin_bound
      (Ll z.1 z.2) S hK hS (hLl z.1 z.2).1 N
    choose MD hMD using fun z : Fin 3 × Fin 3 => exists_compact_iteratedFDerivWithin_bound
      (Rl z.1 z.2) S hK hS (hRl z.1 z.2).1 N
    let M := ∑ z : Fin 3 × Fin 3, (ML z+MR z+MC z+MD z)
    have h0 (z : Fin 3 × Fin 3) : 0 ≤ ML z+MR z+MC z+MD z := by
      linarith [(hML z).1,(hMR z).1,(hMC z).1,(hMD z).1]
    refine ⟨M,Finset.sum_nonneg (fun z _ => h0 z),?_⟩
    intro i j n hn t ht
    have hOne : ML (i,j)+MR (i,j)+MC (i,j)+MD (i,j) ≤ M :=
      Finset.single_le_sum (fun z _ => h0 z) (Finset.mem_univ (i,j))
    have a0 := (hML (i,j)).1
    have b0 := (hMR (i,j)).1
    have c0 := (hMC (i,j)).1
    have d0 := (hMD (i,j)).1
    exact ⟨((hML (i,j)).2 n hn t ht).trans (by linarith),
      ((hMR (i,j)).2 n hn t ht).trans (by linarith),
      ((hMC (i,j)).2 n hn t ht).trans (by linarith),
      ((hMD (i,j)).2 n hn t ht).trans (by linarith)⟩

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- On a variable ORIGINAL high-room record, produce both smooth low families,
both inclusions/transposes/midpoint bounds, and all finite jet caps. Compactness
and UniqueDiffOn are temporary geometric interface facts; the original producer
discharges them from the original room and positivity hypotheses. -/
theorem exists_paired_lows_of_high_room (δ0 δ : ℝ)
    (P : LoweringEHighRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 δ)
    (hK : IsCompact (ParamRoom δ)) (hS : UniqueDiffOn ℝ (ParamRoom δ)) :
    ∃ Ll Rl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
      (∀ i j, ContDiffOn ℝ ∞ (Ll i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Rl i j) (ParamRoom δ)) ∧
      (∀ i j t, t ∈ ParamRoom δ →
        (Ll i j t).comp IH = (JL).comp (P.left i j t) ∧
        (Rl i j t).comp IH = (JL).comp (P.right i j t) ∧
        (I33).comp (Ll i j t) = (v016TransposeL (P.right i j t)).comp JL ∧
        (I33).comp (Rl i j t) = (v016TransposeL (P.left i j t)).comp JL ∧
        ‖Ll i j t‖ ≤ (‖P.left i j t‖+‖P.right i j t‖)/2 ∧
        ‖Rl i j t‖ ≤ (‖P.left i j t‖+‖P.right i j t‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ,
        n ≤ N → ∀ t ∈ ParamRoom δ,
          ‖iteratedFDerivWithin ℝ n (P.left i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (P.right i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Ll i j) (ParamRoom δ) t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Rl i j) (ParamRoom δ) t‖ ≤ M) :=
  exists_finite_smooth_paired_lows (ParamRoom δ) hK hS P.left P.right
    (fun i j => (P.smooth i j).1) (fun i j => (P.smooth i j).2) P.paired

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLoweringEPairedEndpoints
