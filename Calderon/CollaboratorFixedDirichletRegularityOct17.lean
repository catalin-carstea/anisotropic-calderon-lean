import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Calderon.CollaboratorRegularityBaseCaseOct17
import Calderon.CollaboratorRegularityInductionStepOct17

/-! The estimate is obtained from qualitative regularity by the closed graph theorem: on the closed
subspace of pairs `(f, u)` solving the equation, `(f, u) ↦ U` is linear (by uniqueness of `U`)
with closed graph. -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Filter Topology
open scoped InnerProductSpace ContDiff Matrix.Norms.Elementwise

namespace OAI.AnisotropicCalderon.DirichletFamily

open EnergyBridge TauCeti

/-- **Closed graph reduction.** If every element `z` of a closed subspace `Z` admits a lift `U`
with `π U = ρ z` along an injective `π`, then the lift is bounded linearly by `‖z‖`. -/
theorem exists_bounded_lift_of_injective {P Y W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Set P) (h0 : (0 : P) ∈ S)
    (hadd : ∀ z ∈ S, ∀ w ∈ S, z + w ∈ S) (hsmul : ∀ (c : ℝ), ∀ z ∈ S, c • z ∈ S)
    (hS : IsClosed S) (π : Y →L[ℝ] W) (hπ : Function.Injective π) (ρ : P →L[ℝ] W)
    (hlift : ∀ z ∈ S, ∃ U : Y, π U = ρ z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ∃ U : Y, π U = ρ z ∧ ‖U‖ ≤ C * ‖z‖ := by
  let Z : Submodule ℝ P :=
    { carrier := S, add_mem' := fun hz hw => hadd _ hz _ hw, zero_mem' := h0
      smul_mem' := fun c _ hz => hsmul c _ hz }
  have hZ : IsClosed (Z : Set P) := hS
  have : CompleteSpace Z := hZ.completeSpace_coe
  replace hlift : ∀ z ∈ Z, ∃ U : Y, π U = ρ z := hlift
  choose! g hg using hlift
  let G : Z →ₗ[ℝ] Y :=
    { toFun := fun z => g z.1
      map_add' := fun z w => hπ (by
        rw [hg _ (z + w).2, map_add, hg _ z.2, hg _ w.2]
        simp only [Submodule.coe_add, map_add])
      map_smul' := fun c z => hπ (by
        rw [hg _ (c • z).2, map_smul, hg _ z.2]
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]) }
  have hcont : Continuous G := by
    refine G.continuous_of_seq_closed_graph fun zs z y hz hy => ?_
    apply hπ
    change π y = π (g z.1)
    rw [hg _ z.2]
    have h1 : Tendsto (fun n => π (G (zs n))) atTop (𝓝 (π y)) := (π.continuous.tendsto y).comp hy
    have h2 : Tendsto (fun n => π (G (zs n))) atTop (𝓝 (ρ z.1)) := by
      have : (fun n => π (G (zs n))) = fun n => ρ (zs n).1 := funext fun n => hg _ (zs n).2
      rw [this]
      exact (ρ.continuous.tendsto _).comp (continuous_subtype_val.continuousAt.tendsto.comp hz)
    exact tendsto_nhds_unique h1 h2
  let Gc : Z →L[ℝ] Y := ⟨G, hcont⟩
  refine ⟨‖Gc‖, Gc.opNorm_nonneg, fun z hz => ⟨g z, hg z hz, ?_⟩⟩
  change ‖Gc ⟨z, hz⟩‖ ≤ _
  exact Gc.le_opNorm ⟨z, hz⟩

/-- `exists_bounded_lift_of_injective` on a product, lifting the second component. -/
theorem exists_bounded_lift {P₁ P₂ Y W : Type*} [NormedAddCommGroup P₁] [NormedSpace ℝ P₁]
    [CompleteSpace P₁] [NormedAddCommGroup P₂] [NormedSpace ℝ P₂] [CompleteSpace P₂]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Set (P₁ × P₂)) (h0 : ((0 : P₁), (0 : P₂)) ∈ S)
    (hadd : ∀ f u g w, (f, u) ∈ S → (g, w) ∈ S → (f + g, u + w) ∈ S)
    (hsmul : ∀ (c : ℝ) f u, (f, u) ∈ S → (c • f, c • u) ∈ S)
    (hS : IsClosed S) (π : Y →L[ℝ] W) (hπ : Function.Injective π) (ρ : P₂ →L[ℝ] W)
    (hlift : ∀ f u, (f, u) ∈ S → ∃ U : Y, π U = ρ u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f u, (f, u) ∈ S → ∃ U : Y, π U = ρ u ∧ ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  obtain ⟨C, hC, h⟩ := exists_bounded_lift_of_injective S h0 (fun z hz w hw => hadd _ _ _ _ hz hw)
    (fun c z hz => hsmul c _ _ hz) hS π hπ (ρ.comp (ContinuousLinearMap.snd ℝ P₁ P₂))
    (fun z hz => hlift z.1 z.2 hz)
  refine ⟨C, hC, fun f u hfu => ?_⟩
  obtain ⟨U, hU, hn⟩ := h (f, u) hfu
  refine ⟨U, hU, hn.trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  rw [Prod.norm_def]
  exact max_le (by linarith [norm_nonneg u]) (by linarith [norm_nonneg f])

/-- Qualitative regularity: every weak solution with `H^s` forcing lies in `H^{s+2}`. -/
def QualReg (s : ℕ) : Prop :=
  ∀ (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (lam Lam : ℝ),
    ContDiffOn ℝ ∞ a (Metric.closedBall 0 2) →
    TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam →
    ∀ (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens)),
    ∀ (f : BallSobolev s) (u : BallH1Zero),
      (∀ v : BallH1Zero, TauCeti.PDE.energyFormH1L0 hcoeff u v =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
          (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f) v) →
      ∃ U : BallSobolev (s + 2), TauCeti.Wkp.firstOrder (s + 1) U = (u : BallH1)

theorem firstOrder_injective (k : ℕ) :
    Function.Injective (Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) k) := fun U V h => by
  apply Wkp.ext (k + 1)
  rw [← Wkp.value_firstOrder, ← Wkp.value_firstOrder, h]


/-- `exists_bounded_lift` for the solution set of an abstract linear equation `E u = F f`. -/
theorem exists_bounded_lift_eq {P₁ P₂ V Y W : Type*} [NormedAddCommGroup P₁] [NormedSpace ℝ P₁]
    [CompleteSpace P₁] [NormedAddCommGroup P₂] [NormedSpace ℝ P₂] [CompleteSpace P₂]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (E : P₂ →L[ℝ] V →L[ℝ] ℝ) (F : P₁ → V → ℝ)
    (hFadd : ∀ f g v, F (f + g) v = F f v + F g v) (hFsmul : ∀ (c : ℝ) f v, F (c • f) v = c * F f v)
    (hFcont : ∀ v, Continuous fun f => F f v)
    (π : Y →L[ℝ] W) (hπ : Function.Injective π) (ρ : P₂ →L[ℝ] W)
    (hlift : ∀ f u, (∀ v, E u v = F f v) → ∃ U : Y, π U = ρ u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f u, (∀ v, E u v = F f v) →
      ∃ U : Y, π U = ρ u ∧ ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  have hF0 : ∀ v, F 0 v = 0 := fun v => by simpa using hFsmul 0 0 v
  have hS : IsClosed {z : P₁ × P₂ | ∀ v, E z.2 v = F z.1 v} := by
    have : {z : P₁ × P₂ | ∀ v, E z.2 v = F z.1 v} = ⋂ v, {z : P₁ × P₂ | E z.2 v = F z.1 v} := by
      ext z; simp
    rw [this]
    exact isClosed_iInter fun v => isClosed_eq
      ((E.continuous.comp continuous_snd).clm_apply continuous_const)
      ((hFcont v).comp continuous_fst)
  exact exists_bounded_lift {z : P₁ × P₂ | ∀ v, E z.2 v = F z.1 v}
    (fun v => by simp [hF0])
    (fun f u g w hz hw v => by
      simp only [Set.mem_ofPred_eq] at hz hw ⊢
      rw [map_add, add_apply, hz v, hw v, hFadd])
    (fun c f u hz v => by
      simp only [Set.mem_ofPred_eq] at hz ⊢
      rw [map_smul, smul_apply, hz v, hFsmul, smul_eq_mul])
    hS π hπ ρ hlift

section Generic

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- The closed-graph estimate, stated generically so that all spaces share one instance path. -/
theorem bounded_of_qual
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (s : ℕ)
    (hreg : ∀ (f : Wkp mu Omega 2 s) (u : W1p0 mu Omega 2),
      (∀ v : W1p0 mu Omega 2, TauCeti.PDE.energyFormH1L0 hcoeff u v =
        TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s f) v) →
      ∃ U : Wkp mu Omega 2 (s + 2), Wkp.firstOrder (s + 1) U = (u : W1p mu Omega 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Wkp mu Omega 2 s) (u : W1p0 mu Omega 2),
      (∀ v : W1p0 mu Omega 2, TauCeti.PDE.energyFormH1L0 hcoeff u v =
        TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s f) v) →
      ∃ U : Wkp mu Omega 2 (s + 2), Wkp.firstOrder (s + 1) U = (u : W1p mu Omega 2) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  have hFadd : ∀ (f g : Wkp mu Omega 2 s) (v : W1p0 mu Omega 2),
      TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s (f + g)) v =
        TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s f) v +
        TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s g) v := by
    intro f g v
    simp only [TauCeti.PDE.dirichletForcing_apply, Wkp.value_add, inner_add_left]
  have hFsmul : ∀ (c : ℝ) (f : Wkp mu Omega 2 s) (v : W1p0 mu Omega 2),
      TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s (c • f)) v =
        c * TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s f) v := by
    intro c f v
    simp only [TauCeti.PDE.dirichletForcing_apply, Wkp.value_smul, real_inner_smul_left]
  have hFcont : ∀ v : W1p0 mu Omega 2, Continuous fun f : Wkp mu Omega 2 s =>
      TauCeti.PDE.dirichletForcing (Wkp.value (mu := mu) (Omega := Omega) (p := 2) s f) v := by
    intro v
    simp only [TauCeti.PDE.dirichletForcing_apply]
    exact ((Wkp.valueL s).continuous).inner continuous_const
  have hinj : Function.Injective (Wkp.firstOrderL (mu := mu) (Omega := Omega) (p := 2) (s + 1)) :=
    fun U V h => Wkp.ext (s + 2) (by
      rw [← Wkp.value_firstOrder, ← Wkp.value_firstOrder]
      exact congrArg W1p.value h)
  have key := exists_bounded_lift_eq (P₁ := Wkp mu Omega 2 s) (P₂ := W1p0 mu Omega 2)
    (V := W1p0 mu Omega 2) (Y := Wkp mu Omega 2 (s + 2)) (W := W1p mu Omega 2)
    (TauCeti.PDE.energyFormH1L0 hcoeff) _ hFadd hFsmul hFcont _ hinj
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL hreg
  exact key

end Generic

theorem fixedDirichletRegularity_bound_of_qualReg (hreg : ∀ s, QualReg s) (s : ℕ)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev s) (u : BallH1Zero),
      (∀ v : BallH1Zero, TauCeti.PDE.energyFormH1L0 hcoeff u v =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
          (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f) v) →
      ∃ U : BallSobolev (s + 2),
        TauCeti.Wkp.firstOrder (s + 1) U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖) :=
  bounded_of_qual hcoeff s fun f u hu => hreg s a lam Lam hsmooth hell hcoeff f u hu

theorem fixedDirichletRegularity_of_qualReg (hreg : ∀ s, QualReg s) :
    FixedDirichletRegularity :=
  fun s a lam Lam hsmooth hell hcoeff =>
    fixedDirichletRegularity_bound_of_qualReg hreg s a lam Lam hsmooth hell hcoeff

/-- The `H¹₀` equation of `QualReg`, as explicit integrals against `H¹₀`. -/
theorem integral_eq_of_qualReg_hyp {a : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens))
    {f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)} {u : BallH1Zero}
    (hu : ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1L0 hcoeff u v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v)
    (φ : W1p (volume : Measure R3) ballOpens 2)
    (hφ : φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2) :
    ∫ x in (ballOpens : Set R3), TauCeti.PDE.matrixBilinearForm (a x) (W1p.gradient φ x)
        (W1p.gradient (u : BallH1) x) =
      ∫ x in (ballOpens : Set R3), f x * W1p.value φ x := by
  have h := hu ⟨φ, hφ⟩
  rw [Regularity.energyFormH1L0_eq_integral, TauCeti.PDE.dirichletForcing_apply_eq_setIntegral] at h
  exact h

theorem qualReg_zero : QualReg 0 := by
  intro a lam Lam hsmooth hell hcoeff f u hu
  obtain ⟨U, hU⟩ := Regularity.exists_H2 hsmooth hell u.2
    (integral_eq_of_qualReg_hyp hcoeff (f := Wkp.value 0 f) hu)
  exact ⟨U, hU⟩

theorem qualReg (s : ℕ) : QualReg s := by
  intro a lam Lam hsmooth hell hcoeff f u hu
  have hreg : ∀ m, Regularity.HO.RegAt a m := fun m =>
    Nat.rec (Regularity.HO.regAt_zero hsmooth hell)
      (fun m ih => Regularity.HO.regAt_succ hsmooth hell m ih) m
  have hH := hreg s (Wkp.value s f) (Regularity.HO.mem_Hs.mpr ⟨f, rfl⟩) (u : BallH1) u.2
    (integral_eq_of_qualReg_hyp hcoeff hu)
  obtain ⟨U, hU⟩ := Regularity.HO.exists_of_value_mem_Hs (s + 1) u hH
  exact ⟨U, hU⟩

/-- **Fixed-ball Dirichlet regularity.** Qualitative `H^{s+2}` regularity (`qualReg`, by induction
on `s` from the `H²` base case `Regularity.exists_H2`) plus the closed graph theorem. -/
theorem fixedDirichletRegularity : FixedDirichletRegularity :=
  fixedDirichletRegularity_of_qualReg qualReg

end OAI.AnisotropicCalderon.DirichletFamily
