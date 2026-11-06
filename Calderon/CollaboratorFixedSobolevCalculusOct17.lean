import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Calderon.CollaboratorWkpCalculusOct17

/-! Task 06 (see 06-sobolev-calculus.md).

Differentiation is `WkpCalculus.dL`.  Multiplication is built by induction on the order: the
product `φ u ∈ W^{k+1,2}` is reconstructed (`WkpCalculus.ofPartials`) from its first-order part
`φ u ∈ W^{1,2}` and its partial derivatives `φ ∂ᵢu + (∂ᵢφ) u ∈ W^{k,2}`, which are products of
order `k` with `φ` and with `∂ᵢφ`. -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff Gradient InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily

open EnergyBridge WkpCalculus TauCeti

variable {Ω : Opens R3}

theorem memLp_mul (φ : R3 → ℝ) (hφ : Continuous φ) (M : ℝ) (hM : ∀ x, |φ x| ≤ M)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict Ω)) :
    MemLp (fun x => φ x * f x) 2 ((volume : Measure R3).restrict Ω) :=
  MemLp.of_le_mul (Lp.memLp f) (hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

/-- Multiplication by a bounded continuous function on `L²(Ω)`, as a linear map. -/
def mulLin (φ : R3 → ℝ) (hφ : Continuous φ) (M : ℝ) (hM : ∀ x, |φ x| ≤ M) :
    Lp ℝ 2 ((volume : Measure R3).restrict Ω) →ₗ[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict Ω) where
  toFun f := (memLp_mul φ hφ M hM f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_mul φ hφ M hM (f + g)).coeFn_toLp, (memLp_mul φ hφ M hM f).coeFn_toLp,
      (memLp_mul φ hφ M hM g).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((memLp_mul φ hφ M hM f).toLp _) ((memLp_mul φ hφ M hM g).toLp _)]
      with x h1 h2 h3 h4 h5
    rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_mul φ hφ M hM (c • f)).coeFn_toLp, (memLp_mul φ hφ M hM f).coeFn_toLp,
      Lp.coeFn_smul c f, Lp.coeFn_smul c ((memLp_mul φ hφ M hM f).toLp _)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

theorem mulLin_bound (φ : R3 → ℝ) (hφ : Continuous φ) (M : ℝ) (hM : ∀ x, |φ x| ≤ M)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict Ω)) : ‖mulLin φ hφ M hM f‖ ≤ M * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [(memLp_mul φ hφ M hM f).coeFn_toLp] with x hx
  change ‖((memLp_mul φ hφ M hM f).toLp _ : Lp ℝ 2 _) x‖ ≤ _
  rw [hx, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

/-- Multiplication by a bounded continuous function on `L²(Ω)`. -/
def mulL0 (φ : R3 → ℝ) (hφ : Continuous φ) (M : ℝ) (hM : ∀ x, |φ x| ≤ M) :
    Lp ℝ 2 ((volume : Measure R3).restrict Ω) →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict Ω) :=
  (mulLin φ hφ M hM).mkContinuous M (mulLin_bound φ hφ M hM)

theorem mulL0_apply_ae (φ : R3 → ℝ) (hφ : Continuous φ) (M : ℝ) (hM : ∀ x, |φ x| ≤ M)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict Ω)) :
    ⇑(mulL0 φ hφ M hM f) =ᵐ[(volume : Measure R3).restrict Ω] fun x => φ x * f x :=
  (memLp_mul φ hφ M hM f).coeFn_toLp

theorem norm_mulL0_le (φ : R3 → ℝ) (hφ : Continuous φ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, |φ x| ≤ M) : ‖mulL0 (Ω := Ω) φ hφ M hM‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM0 (mulLin_bound φ hφ M hM)

theorem norm_firstOrder_le : ∀ (k : ℕ) (u : Wkp (volume : Measure R3) Ω 2 (k + 1)),
    ‖Wkp.firstOrder k u‖ ≤ ‖u‖
  | 0, _ => le_rfl
  | k + 1, u => (norm_firstOrder_le k _).trans (Wkp.norm_lowerOrder_le (k + 1) u)

theorem gradient_apply_coord {φ : R3 → ℝ} (x : R3) (i : Fin 3) :
    gradient φ x i = fderiv ℝ φ x (e i) := by
  rw [← inner_gradient_left (𝕜 := ℝ), EuclideanSpace.inner_single_right]
  simp

/-- The multiplication statement at a fixed order. -/
def MulAt (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : R3 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ M : ℝ, 0 ≤ M →
    (∀ j : ℕ, j ≤ k + 1 → ∀ x : R3, ‖iteratedFDeriv ℝ j φ x‖ ≤ M) →
    ∃ T : Wkp (volume : Measure R3) Ω 2 k →L[ℝ] Wkp (volume : Measure R3) Ω 2 k,
      (∀ f, ⇑(Wkp.value k (T f)) =ᵐ[(volume : Measure R3).restrict Ω]
          fun x => φ x * Wkp.value k f x) ∧ ‖T‖ ≤ C * M

theorem mulAt_zero : MulAt (Ω := Ω) 0 := by
  refine ⟨1, zero_le_one, fun φ hφ _ M hM hb => ?_⟩
  have hφM : ∀ x, |φ x| ≤ M := fun x => by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (Nat.zero_le _) x
  refine ⟨mulL0 φ hφ.continuous M hφM, fun f => ?_, ?_⟩
  · simpa only [Wkp.value_zero] using mulL0_apply_ae φ hφ.continuous M hφM f
  · rw [one_mul]
    exact norm_mulL0_le φ hφ.continuous hM hφM


theorem norm_apply_e_le (i : Fin 3) : ‖ContinuousLinearMap.apply ℝ ℝ (e i)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [ContinuousLinearMap.apply_apply, one_mul]
    refine (f.le_opNorm (e i)).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one]

/-- Bounds on the derivatives of `∂ᵢφ` from bounds on the derivatives of `φ`. -/
theorem partial_bounds {φ : R3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 3) {M : ℝ} {k : ℕ}
    (hb : ∀ j : ℕ, j ≤ k + 2 → ∀ x : R3, ‖iteratedFDeriv ℝ j φ x‖ ≤ M) :
    ∀ j : ℕ, j ≤ k + 1 → ∀ x : R3,
      ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x (e i)) x‖ ≤ M := by
  intro j hj x
  have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by simp)
  have hcomp : (fun x => fderiv ℝ φ x (e i)) =
      ⇑(ContinuousLinearMap.apply ℝ ℝ (e i)) ∘ fderiv ℝ φ := rfl
  rw [hcomp]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hd.contDiffAt
    (by exact_mod_cast le_top)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  calc _ ≤ 1 * M := mul_le_mul (norm_apply_e_le i) (hb (j + 1) (by omega) x)
          (norm_nonneg _) zero_le_one
    _ = M := one_mul M

theorem mulAt_succ (k : ℕ) (ih : MulAt (Ω := Ω) k) : MulAt (Ω := Ω) (k + 1) := by
  obtain ⟨C, hC, hT⟩ := ih
  set Dn : ℝ := ∑ i, ‖dL (Ω := Ω) i k‖ with hDn
  have hDn0 : 0 ≤ Dn := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨2 + k * (C * (Dn + 3)), by positivity, fun φ hφ hsupp M hM hb => ?_⟩
  have hb' : ∀ j : ℕ, j ≤ k + 1 → ∀ x : R3, ‖iteratedFDeriv ℝ j φ x‖ ≤ M :=
    fun j hj => hb j (by omega)
  set ψ : Fin 3 → R3 → ℝ := fun i x => fderiv ℝ φ x (e i) with hψdef
  have hψ : ∀ i, ContDiff ℝ ∞ (ψ i) := fun i =>
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hψsupp : ∀ i, HasCompactSupport (ψ i) := fun i => hsupp.fderiv_apply ℝ (e i)
  choose Tφ hTφv hTφn using hT φ hφ hsupp M hM hb'
  choose Tψ hTψv hTψn using fun i => hT (ψ i) (hψ i) (hψsupp i) M hM (partial_bounds hφ i hb)
  have hφM : ∀ x ∈ Ω, |φ x| ≤ M := fun x _ => by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (Nat.zero_le _) x
  have hgM : ∀ x ∈ Ω, ‖gradient φ x‖ ≤ M := fun x _ => by
    rw [norm_gradient_eq_norm_fderiv, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact hb 1 (by omega) x
  let w : Wkp (volume : Measure R3) Ω 2 (k + 1) → W1p (volume : Measure R3) Ω 2 := fun u =>
    W1p.contDiffSMul φ hφ hM hφM hgM (Wkp.firstOrder k u)
  let g : Wkp (volume : Measure R3) Ω 2 (k + 1) → Fin 3 → Wkp (volume : Measure R3) Ω 2 k :=
    fun u i => Tφ (dL i k u) + Tψ i (Wkp.lowerOrder k u)
  have hg : ∀ u i, ⇑(Wkp.value k (g u i)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => W1p.gradient (w u) x i := by
    intro u i
    filter_upwards [Lp.coeFn_add (Wkp.value k (Tφ (dL i k u)))
        (Wkp.value k (Tψ i (Wkp.lowerOrder k u))),
      hTφv (dL i k u), hTψv i (Wkp.lowerOrder k u), value_d i k u,
      W1p.gradient_contDiffSMul_ae hφ hM hφM hgM (Wkp.firstOrder k u)] with x h1 h2 h3 h4 h5
    simp only [g, w, Wkp.value_add]
    rw [h1, Pi.add_apply, h2, h3, dL_apply, h4, h5]
    have hv : W1p.value (Wkp.firstOrder k u) = Wkp.value k (Wkp.lowerOrder k u) := by
      rw [Wkp.value_firstOrder, Wkp.value_succ]
    rw [hv, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, gradient_apply_coord]
    simp only [smul_eq_mul, ψ]
    ring
  let Tfun : Wkp (volume : Measure R3) Ω 2 (k + 1) → Wkp (volume : Measure R3) Ω 2 (k + 1) :=
    fun u => ofPartials k (w u) (g u) (hg u)
  have hTval : ∀ u, ⇑(Wkp.value (k + 1) (Tfun u)) =ᵐ[(volume : Measure R3).restrict Ω]
      fun x => φ x * Wkp.value (k + 1) u x := by
    intro u
    simp only [Tfun, value_ofPartials]
    filter_upwards [W1p.value_contDiffSMul_ae hφ hM hφM hgM (Wkp.firstOrder k u)] with x hx
    rw [hx, Wkp.value_firstOrder, smul_eq_mul]
  let Tlin : Wkp (volume : Measure R3) Ω 2 (k + 1) →ₗ[ℝ] Wkp (volume : Measure R3) Ω 2 (k + 1) :=
    { toFun := Tfun
      map_add' := fun u v => by
        apply Wkp.ext (k + 1)
        rw [Wkp.value_add]
        apply Lp.ext
        filter_upwards [hTval (u + v), hTval u, hTval v, Lp.coeFn_add (Wkp.value (k + 1) u)
          (Wkp.value (k + 1) v), Lp.coeFn_add (Wkp.value (k + 1) (Tfun u))
          (Wkp.value (k + 1) (Tfun v))] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, Wkp.value_add, h4, Pi.add_apply, mul_add]
      map_smul' := fun c u => by
        apply Wkp.ext (k + 1)
        rw [Wkp.value_smul]
        apply Lp.ext
        filter_upwards [hTval (c • u), hTval u, Lp.coeFn_smul c (Wkp.value (k + 1) u),
          Lp.coeFn_smul c (Wkp.value (k + 1) (Tfun u))] with x h1 h2 h4 h5
        rw [h1, RingHom.id_apply, h5, Pi.smul_apply, h2, Wkp.value_smul, h4, Pi.smul_apply,
          smul_eq_mul, smul_eq_mul]
        ring }
  have hbound : ∀ u, ‖Tlin u‖ ≤ ((2 + k * (C * (Dn + 3))) * M) * ‖u‖ := by
    intro u
    change ‖Tfun u‖ ≤ _
    have hu0 := norm_nonneg u
    have h1 := norm_ofPartials_le k (w u) (g u) (hg u)
    have hw : ‖w u‖ ≤ 2 * M * ‖u‖ :=
      (W1p.norm_contDiffSMul_le hφ hM hφM hgM (Wkp.firstOrder k u)).trans
        (mul_le_mul_of_nonneg_left (norm_firstOrder_le k u) (by positivity))
    have hgi : ∀ i, ‖g u i‖ ≤ C * M * ‖dL (Ω := Ω) i k‖ * ‖u‖ + C * M * ‖u‖ := by
      intro i
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (Tφ.le_opNorm _).trans ?_
        calc ‖Tφ‖ * ‖dL i k u‖ ≤ (C * M) * (‖dL (Ω := Ω) i k‖ * ‖u‖) :=
              mul_le_mul hTφn ((dL i k).le_opNorm u) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      · refine ((Tψ i).le_opNorm _).trans ?_
        exact mul_le_mul (hTψn i) (Wkp.norm_lowerOrder_le k u) (norm_nonneg _) (by positivity)
    have hsum : ∑ i, ‖g u i‖ ≤ C * M * (Dn + 3) * ‖u‖ := by
      refine (Finset.sum_le_sum fun i _ => hgi i).trans (le_of_eq ?_)
      simp only [Fin.sum_univ_three, hDn]
      ring
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc ‖Tfun u‖ ≤ ‖w u‖ + k * ∑ i, ‖g u i‖ := h1
      _ ≤ 2 * M * ‖u‖ + k * (C * M * (Dn + 3) * ‖u‖) :=
          add_le_add hw (mul_le_mul_of_nonneg_left hsum hk)
      _ = _ := by ring
  refine ⟨Tlin.mkContinuous _ hbound, fun f => ?_, ?_⟩
  · exact hTval f
  · exact LinearMap.mkContinuous_norm_le _ (by positivity) hbound

theorem mulAt : ∀ k, MulAt (Ω := Ω) k
  | 0 => mulAt_zero
  | k + 1 => mulAt_succ k (mulAt k)

/-- Prove the exact composite interface. -/
theorem fixedSobolevCalculus : FixedSobolevCalculus :=
  ⟨fun k => mulAt (Ω := ballOpens) k, fun k i => ⟨dL i k, fun u => value_d i k u⟩⟩

end OAI.AnisotropicCalderon.DirichletFamily
