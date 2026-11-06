import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.PDE.Regularity.Basic
import TauCeti.Analysis.Sobolev.DifferenceQuotient
import TauCeti.Analysis.Sobolev.W1p.Density

/-! Whole-space `H²` regularity for variable Lipschitz principal coefficients (helper for task 05).

Generalizes `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq` (constant coefficient) to a
variable coefficient matrix with Lipschitz entries, by the difference-quotient method with the
extra commutator term `∫ (Dᵗ a) (∇u)(· + t w) · ∇v`. -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped Matrix InnerProductSpace
namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE

section Generic

/-! The argument is carried out for a general Euclidean space and Haar measure, so that all
instance paths agree with those of the Tau Ceti energy-form API; it is specialized to `R3` at the
end. -/

variable {ι : Type*} [Fintype ι]

/-- A crude entrywise bound for a square matrix acting bilinearly on vectors. -/
lemma abs_dotProduct_mulVec_le_of_entry (M : Matrix ι ι ℝ) {c : ℝ}
    (hc : ∀ i j, |M i j| ≤ c) (η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ (M *ᵥ ξ)| ≤ ((Fintype.card ι : ℝ) ^ 2 * c) * ‖η‖ * ‖ξ‖ := by
  have hη : ∀ i, |η i| ≤ ‖η‖ := fun i => by simpa using PiLp.norm_apply_le η i
  have hξ : ∀ j, |ξ j| ≤ ‖ξ‖ := fun j => by simpa using PiLp.norm_apply_le ξ j
  have hterm : ∀ i j, |η i * (M i j * ξ j)| ≤ c * ‖η‖ * ‖ξ‖ := by
    intro i j
    rw [abs_mul, abs_mul]
    calc |η i| * (|M i j| * |ξ j|) ≤ ‖η‖ * (c * ‖ξ‖) := by
          gcongr
          all_goals first
            | exact hη i | exact hξ j | exact hc i j | exact (abs_nonneg _).trans (hc i j)
      _ = c * ‖η‖ * ‖ξ‖ := by ring
  calc |η ⬝ᵥ (M *ᵥ ξ)| = |∑ i, ∑ j, η i * (M i j * ξ j)| := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |η i * (M i j * ξ j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, c * ‖η‖ * ‖ξ‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = ((Fintype.card ι : ℝ) ^ 2 * c) * ‖η‖ * ‖ξ‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

lemma continuous_coeff {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) : Continuous a :=
  continuous_pi fun i => continuous_pi fun j => (hlip i j).continuous

lemma aestronglyMeasurable_coeff {b : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hb : Continuous b) {μ : Measure (EuclideanSpace ℝ ι)} : AEStronglyMeasurable b μ := by
  have hb' : @Continuous (EuclideanSpace ℝ ι) (ι → ι → ℝ) _ _ b := hb
  exact hb'.aestronglyMeasurable

/-- The entries of the shifted coefficient difference are bounded by the Lipschitz constant. -/
lemma coeff_shift_bound {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) (w : EuclideanSpace ℝ ι) (t : ℝ)
    (x η ξ : EuclideanSpace ℝ ι) :
    |η ⬝ᵥ ((a (x + t • w) - a x) *ᵥ ξ)|
      ≤ ((Fintype.card ι : ℝ) ^ 2 * ((K : ℝ) * ‖w‖) * |t|) * ‖η‖ * ‖ξ‖ := by
  have hent : ∀ i j, |(a (x + t • w) - a x) i j| ≤ (K : ℝ) * (|t| * ‖w‖) := by
    intro i j
    have := (hlip i j).dist_le_mul (x + t • w) x
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
    simpa using this
  have := abs_dotProduct_mulVec_le_of_entry _ hent η ξ
  convert this using 2
  ring

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

/-- Admissible (essentially bounded) principal coefficient field, with no lower-order terms. -/
@[inline, reducible] def CoeffOK (mu : Measure (EuclideanSpace ℝ ι)) (b : EuclideanSpace ℝ ι → Matrix ι ι ℝ) :
    Prop :=
  MemLp (fun x => energyIntegrand (b x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
    ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
    (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))

omit [mu.IsAddHaarMeasure] in
/-- Bounded continuous principal coefficients are admissible. -/
lemma memLp_coeff {b : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : Continuous b)
    (hbound : ∀ x (η ξ : EuclideanSpace ℝ ι), |η ⬝ᵥ (b x *ᵥ ξ)| ≤ L * ‖η‖ * ‖ξ‖) :
    CoeffOK mu b :=
  memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hL (aestronglyMeasurable_coeff hb)
    aestronglyMeasurable_const aestronglyMeasurable_const (fun x _ => hbound x)
    (by simp) (by simp)

/-- The energy form is additive in the principal coefficient. -/
lemma energyFormH1_sub_coeff {a a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : CoeffOK mu a) (ha' : CoeffOK mu a') (u v : W1p mu ⊤ 2) :
    energyFormH1 a' 0 0 u v - energyFormH1 a 0 0 u v
      = energyFormH1 (fun x => a' x - a x) 0 0 u v := by
  rw [energyFormH1_def, energyFormH1_def, energyFormH1_def,
    ← integral_sub (PDE.integrable_energyIntegrand_jetField ha' u v)
      (PDE.integrable_energyIntegrand_jetField ha u v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [matrixBilinearForm_apply, Matrix.sub_mulVec, dotProduct_sub]

/-- Translation moves across the variable-coefficient energy form, shifting the coefficient. -/
lemma energyFormH1_translate_var (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    {h k : EuclideanSpace ℝ ι} (hk : h + k = 0) (u v : W1p mu ⊤ 2) :
    energyFormH1 a 0 0 u (W1p.translate (Set.mapsTo_univ (· + k) _) v)
      = energyFormH1 (fun x => a (x + h)) 0 0
          (W1p.translate (Set.mapsTo_univ (· + h) _) u) v := by
  have hinv : ∀ F : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F (x + h) ∂mu
        = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F x ∂mu := by
    intro F
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_add_right_eq_self F h
  have hcancel : ∀ x : EuclideanSpace ℝ ι, x + h + k = x := fun x => by
    rw [add_assoc, hk, add_zero]
  rw [energyFormH1_def, energyFormH1_def]
  simp only [energyIntegrand_apply, jetField_apply, Pi.zero_apply, driftForm_apply,
    massForm_apply, add_zero, zero_mul, inner_zero_left]
  calc ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
        matrixBilinearForm (a x)
          (W1p.gradient (W1p.translate (Set.mapsTo_univ (· + k) _) v) x)
          (W1p.gradient u x) ∂mu
      = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm (a x) (W1p.gradient v (x + k)) (W1p.gradient u x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_translate_ae (Set.mapsTo_univ (· + k) _) v] with x hx
        rw [hx]
    _ = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm (a (x + h)) (W1p.gradient v (x + h + k))
            (W1p.gradient u (x + h)) ∂mu :=
        (hinv fun y => matrixBilinearForm (a y) (W1p.gradient v (y + k))
          (W1p.gradient u y)).symm
    _ = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm (a (x + h)) (W1p.gradient v x)
            (W1p.gradient (W1p.translate (Set.mapsTo_univ (· + h) _) u) x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_translate_ae (Set.mapsTo_univ (· + h) _) u] with x hx
        rw [hx, hcancel]

lemma eLpNorm_comp_add_top {F : Type*} [NormedAddCommGroup F]
    (G : EuclideanSpace ℝ ι → F)
    (hG : AEStronglyMeasurable G
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (h : EuclideanSpace ℝ ι) :
    eLpNorm (fun x => G (x + h)) 2
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      = eLpNorm G 2
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
  simp only [Opens.coe_top, Measure.restrict_univ] at hG ⊢
  exact eLpNorm_comp_measurePreserving hG (measurePreserving_add_right mu h)

/-- The whole-space difference quotient (abbreviation). -/
@[inline, reducible] def dq (w : EuclideanSpace ℝ ι) (t : ℝ) (U : W1p mu ⊤ 2) : W1p mu ⊤ 2 :=
  W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) U

/-- The whole-space translate (abbreviation). -/
@[inline, reducible] def tr (h : EuclideanSpace ℝ ι) (U : W1p mu ⊤ 2) : W1p mu ⊤ 2 :=
  W1p.translate (V := ⊤) (Set.mapsTo_univ (· + h) _) U

/-- Whole-space translation preserves the `W^{1,2}` norm. -/
lemma norm_tr (h : EuclideanSpace ℝ ι) (u : W1p mu ⊤ 2) : ‖tr h u‖ = ‖u‖ := by
  have hv : ‖W1p.value (tr h u)‖ = ‖W1p.value u‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (W1p.value_translate_ae _ u),
      eLpNorm_comp_add_top _ (Lp.aestronglyMeasurable _) h]
  have hg : ‖W1p.gradient (tr h u)‖ = ‖W1p.gradient u‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (W1p.gradient_translate_ae _ u),
      eLpNorm_comp_add_top _ (Lp.aestronglyMeasurable _) h]
  have h1 := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq (tr h u)
  have h2 := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  rw [hv, hg, ← h2] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

lemma tr_eq_add_smul_dq (w : EuclideanSpace ℝ ι) {t : ℝ} (ht : t ≠ 0)
    (U : W1p mu ⊤ 2) : tr (t • w) U = U + t • dq w t U := by
  have h1 : dq w t U = t⁻¹ • (tr (t • w) U - U) := by
    have h0 := W1p.differenceQuotient_def (mu := mu) (p := 2) le_rfl w t
      (Set.mapsTo_univ (· + t • w) _) U
    rw [W1p.restrictL_self] at h0
    exact h0
  rw [h1, smul_smul, mul_inv_cancel₀ ht, one_smul]
  abel

/-- The discrete integration-by-parts identity with the commutator term. -/
lemma energy_dq_identity {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hcoA : CoeffOK mu a) (w : EuclideanSpace ℝ ι) {t : ℝ} (ht : t ≠ 0)
    (hcoAh : CoeffOK mu (fun x => a (x + t • w))) (U : W1p mu ⊤ 2) :
    energyFormH1 a 0 0 U (dq w (-t) (dq w t U))
      = -energyFormH1 a 0 0 (dq w t U) (dq w t U)
        - t⁻¹ * energyFormH1 (fun x => a (x + t • w) - a x) 0 0 (tr (t • w) U) (dq w t U) := by
  have hk : t • w + (-t) • w = 0 := by rw [← add_smul]; simp
  have hright : energyFormH1 a 0 0 U (dq w (-t) (dq w t U))
      = (-t)⁻¹ * (energyFormH1 a 0 0 U (tr ((-t) • w) (dq w t U))
        - energyFormH1 a 0 0 U (dq w t U)) := by
    rw [dq, W1p.differenceQuotient_def, W1p.restrictL_self, ← energyFormH1L_apply hcoA]
    simp only [map_smul, map_sub, energyFormH1L_apply, smul_eq_mul]
  have e2 : energyFormH1 a 0 0 U (tr ((-t) • w) (dq w t U))
      = energyFormH1 (fun x => a (x + t • w)) 0 0 (tr (t • w) U) (dq w t U) :=
    energyFormH1_translate_var a hk U (dq w t U)
  have e3 := energyFormH1_sub_coeff hcoA hcoAh (tr (t • w) U) (dq w t U)
  have e4 : energyFormH1 a 0 0 (tr (t • w) U) (dq w t U)
      = energyFormH1 a 0 0 U (dq w t U) + t * energyFormH1 a 0 0 (dq w t U) (dq w t U) := by
    rw [tr_eq_add_smul_dq w ht U, ← energyFormH1L_apply hcoA]
    simp only [map_add, map_smul, add_apply, smul_apply, energyFormH1L_apply, smul_eq_mul]
  rw [hright, e2]
  have hP : energyFormH1 (fun x => a (x + t • w)) 0 0 (tr (t • w) U) (dq w t U)
      = energyFormH1 a 0 0 U (dq w t U) + t * energyFormH1 a 0 0 (dq w t U) (dq w t U)
        + energyFormH1 (fun x => a (x + t • w) - a x) 0 0 (tr (t • w) U) (dq w t U) := by
    linarith [e3, e4]
  rw [hP, inv_neg]
  field_simp
  ring

lemma le_of_quadratic {lam X α β : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hkey : lam * X ^ 2 ≤ α * X + β) : X ≤ 1 + (α + β) / lam := by
  have hC : 0 ≤ (α + β) / lam := by positivity
  rcases le_or_gt X 1 with hX | hX
  · linarith
  · have h2 : lam * X ≤ α + β := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have : X ≤ (α + β) / lam := by rw [le_div_iff₀ hlam]; linarith
    linarith

lemma weak_eq_dq {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u) (v : W1p mu ⊤ 2) :
    energyFormH1 a 0 0 (u : W1p mu ⊤ 2) v = ⟪f, W1p.value v⟫_ℝ := by
  have hv0 : v ∈ w1p0Submodule mu ⊤ 2 := W1p.mem_w1p0Submodule_top (by norm_num) _
  have h1 := hu ⟨v, hv0⟩
  rw [dirichletForcing_apply] at h1
  exact h1

lemma lower_energy [DecidableEq ι] {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {lam Lam : ℝ} (hell : UniformlyEllipticOn (Set.univ : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hacont : Continuous a) (g : W1p mu ⊤ 2) :
    lam * ‖W1p.gradient g‖ ^ 2 ≤ energyFormH1 a 0 0 g g := by
  have hell' : UniformlyEllipticOn
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) a lam Lam := by
    simpa using hell
  exact hell'.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (b := 0) (c := 0)
    (gamma := 0) (aestronglyMeasurable_coeff hacont) aestronglyMeasurable_const
    (fun _ _ => rfl) (fun _ _ => by simp) (fun _ _ => le_rfl) _

lemma commutator_bound {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {K : NNReal}
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) (w : EuclideanSpace ℝ ι) {t : ℝ}
    (ht : t ≠ 0) (U : W1p mu ⊤ 2) :
    |t⁻¹ * energyFormH1 (fun x => a (x + t • w) - a x) 0 0 (tr (t • w) U) (dq w t U)|
      ≤ (Fintype.card ι : ℝ) ^ 2 * ((K : ℝ) * ‖w‖) * (‖U‖ * ‖dq w t U‖) := by
  have hn := norm_energyFormH1_le_of_bounds (a := fun x => a (x + t • w) - a x)
    (b := 0) (c := 0) (beta := 0) (gamma := 0)
    (Lam := (Fintype.card ι : ℝ) ^ 2 * ((K : ℝ) * ‖w‖) * |t|) (by positivity)
    (fun x _ η ξ => coeff_shift_bound hlip w t x η ξ) le_rfl le_rfl
    (fun _ _ => by simp) (fun _ _ => by simp) (tr (t • w) U) (dq w t U)
  rw [Real.norm_eq_abs, add_zero, add_zero, norm_tr] at hn
  rw [abs_mul, abs_inv]
  have htpos : 0 < |t| := abs_pos.mpr ht
  calc |t|⁻¹ * |energyFormH1 (fun x => a (x + t • w) - a x) 0 0 (tr (t • w) U) (dq w t U)|
      ≤ |t|⁻¹ * ((Fintype.card ι : ℝ) ^ 2 * ((K : ℝ) * ‖w‖) * |t| * (‖U‖ * ‖dq w t U‖)) := by
        gcongr
    _ = (Fintype.card ι : ℝ) ^ 2 * ((K : ℝ) * ‖w‖) * (‖U‖ * ‖dq w t U‖) := by
        field_simp

lemma norm_dq_le (w : EuclideanSpace ℝ ι) (t : ℝ) (U : W1p mu ⊤ 2) :
    ‖dq w t U‖ ≤ ‖w‖ * ‖W1p.gradient U‖ + ‖W1p.gradient (dq w t U)‖ := by
  have h1 := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq (dq w t U)
  have h2 : ‖W1p.value (dq w t U)‖ ≤ ‖w‖ * ‖W1p.gradient U‖ :=
    W1p.norm_value_differenceQuotient_le (by norm_num) w t U
  have h3 : 0 ≤ ‖W1p.value (dq w t U)‖ := norm_nonneg _
  have h4 : 0 ≤ ‖W1p.gradient (dq w t U)‖ := norm_nonneg _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [h1]
  nlinarith

/-- **Uniform bound on the difference quotients of the gradient.** For a weak solution with
uniformly elliptic Lipschitz coefficients, `‖∇Dᵗ u‖_{L²}` is bounded independently of `t`. -/
lemma exists_bound_gradient_dq [DecidableEq ι] {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {lam Lam : ℝ} {K : NNReal}
    (hell : UniformlyEllipticOn (Set.univ : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u) (w : EuclideanSpace ℝ ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖W1p.gradient (dq w t (u : W1p mu ⊤ 2))‖ ≤ C := by
  have hsol := weak_eq_dq hu
  obtain ⟨U, hUdef⟩ : ∃ U : W1p mu ⊤ 2, U = (u : W1p mu ⊤ 2) := ⟨_, rfl⟩
  rw [← hUdef]
  rw [← hUdef] at hsol
  have hlam : 0 < lam := hell.pos
  have hacont : Continuous a := continuous_coeff hlip
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (Fintype.card ι : ℝ) ^ 2 * ((K : ℝ) * ‖w‖) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = ‖f‖ * ‖w‖ + M * ‖U‖ := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = M * ‖U‖ * (‖w‖ * ‖W1p.gradient U‖) := ⟨_, rfl⟩
  have hα : 0 ≤ α := by rw [hαdef]; positivity
  have hβ : 0 ≤ β := by rw [hβdef]; positivity
  refine ⟨1 + (α + β) / lam, by positivity, fun t => ?_⟩
  rcases eq_or_ne t 0 with rfl | ht
  · have hg0 : dq w 0 U = 0 := by
      rw [dq, W1p.differenceQuotient_def, inv_zero, zero_smul]
    have hgr : W1p.gradient (0 : W1p mu ⊤ 2) = 0 :=
      (W1p.gradientL_apply _).symm.trans (map_zero _)
    rw [hg0, hgr, norm_zero]
    have : 0 ≤ (α + β) / lam := by positivity
    linarith
  refine le_of_quadratic hlam hα hβ ?_
  have hcoA : CoeffOK mu a := memLp_coeff hell.upper_nonneg hacont
    (fun x η ξ => hell.upper_bound (Set.mem_univ x) η ξ)
  have hcoAh : CoeffOK mu (fun x => a (x + t • w)) := memLp_coeff hell.upper_nonneg
    (hacont.comp (continuous_id.add continuous_const))
    (fun x η ξ => hell.upper_bound (Set.mem_univ _) η ξ)
  have hid := energy_dq_identity hcoA w ht hcoAh U
  rw [hsol] at hid
  have hlow := lower_energy (mu := mu) hell hacont (dq w t U)
  have hfv : |⟪f, W1p.value (dq w (-t) (dq w t U))⟫_ℝ|
      ≤ ‖f‖ * (‖w‖ * ‖W1p.gradient (dq w t U)‖) :=
    (abs_real_inner_le_norm f _).trans (mul_le_mul_of_nonneg_left
      (W1p.norm_value_differenceQuotient_le (by norm_num) w (-t) (dq w t U)) (norm_nonneg f))
  have hbnd := commutator_bound hlip w ht U
  rw [← hM] at hbnd
  have hgn := norm_dq_le w t U
  have hfin : M * (‖U‖ * ‖dq w t U‖)
      ≤ M * (‖U‖ * (‖w‖ * ‖W1p.gradient U‖ + ‖W1p.gradient (dq w t U)‖)) := by
    gcongr
  have ha := neg_le_abs ⟪f, W1p.value (dq w (-t) (dq w t U))⟫_ℝ
  have hb := neg_le_abs
    (t⁻¹ * energyFormH1 (fun x => a (x + t • w) - a x) 0 0 (tr (t • w) U) (dq w t U))
  have hαβ : α * ‖W1p.gradient (dq w t U)‖ + β = ‖f‖ * (‖w‖ * ‖W1p.gradient (dq w t U)‖)
      + M * (‖U‖ * (‖w‖ * ‖W1p.gradient U‖ + ‖W1p.gradient (dq w t U)‖)) := by
    rw [hαdef, hβdef]; ring
  rw [hαβ]
  linarith [hid]

/-- The second-order weak directional derivatives of a whole-space weak solution with Lipschitz
coefficients. -/
lemma exists_hasWeakLineDerivOn_gradient_var [DecidableEq ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {K : NNReal}
    (hell : UniformlyEllipticOn (Set.univ : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u) (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      HasWeakLineDerivOn mu ⊤ (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ) G w := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_gradient_dq hell hlip hu w
  have hloc : LocallyIntegrableOn
      (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ)
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) mu := by
    simpa using
      ((W1p.hasWeakFDerivOn (u : W1p mu ⊤ 2)).hasWeakLineDerivOn y).locallyIntegrableOn_deriv
  have hglobal : ∀ t : ℝ, eLpNorm
      (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu ⊤ 2) (x + t • w), y⟫_ℝ
        - ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ)) 2
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      ≤ ENNReal.ofReal (‖y‖ * C) := by
    intro t
    set g := W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2)
    have hae : (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu ⊤ 2) (x + t • w), y⟫_ℝ
          - ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ))
        =ᵐ[mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))]
          fun x => ⟪W1p.gradient g x, y⟫_ℝ := by
      filter_upwards [W1p.gradient_differenceQuotient_ae le_rfl w t
        (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2)] with x hx
      rw [hx, inner_smul_left, inner_sub_left]
      simp [mul_sub]
    rw [eLpNorm_congr_ae hae]
    calc eLpNorm (fun x => ⟪W1p.gradient g x, y⟫_ℝ) 2
          (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
        ≤ eLpNorm (‖y‖ • (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) 2
            (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) :=
          have hmeas : AEStronglyMeasurable (fun x => ⟪W1p.gradient g x, y⟫_ℝ)
              (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) :=
            (Lp.aestronglyMeasurable (W1p.gradient g)).inner_const
          eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall fun x => by
            rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, mul_comm]
            exact abs_real_inner_le_norm _ y)
      _ = ‖y‖ₑ * eLpNorm (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
            (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
          rw [eLpNorm_const_smul, enorm_norm]
      _ = ‖y‖ₑ * ENNReal.ofReal ‖W1p.gradient g‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      _ ≤ ‖y‖ₑ * ENNReal.ofReal C := by
          gcongr
          exact hC t
      _ = ENNReal.ofReal (‖y‖ * C) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg y)]
  obtain ⟨G, -, hG⟩ := exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le
    hloc w (by positivity : 0 ≤ ‖y‖ * C) fun K hK _ => Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun t =>
        le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono hK le_rfl)) (hglobal t))
  exact ⟨G, hG⟩

/-- Generic form of the whole-space `H²` regularity for Lipschitz coefficients. -/
theorem exists_lowerOrder_eq_var [DecidableEq ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {K : NNReal}
    (hell : UniformlyEllipticOn (Set.univ : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ U : Wkp mu ⊤ 2 2, Wkp.lowerOrder 1 U = (u : W1p mu ⊤ 2) :=
  W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun i j => exists_hasWeakLineDerivOn_gradient_var hell hlip hu
      (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)

end Generic

/-- Whole-space `H²` regularity of weak solutions of `-div(a ∇u) = f` with `a` uniformly elliptic
and Lipschitz. -/
theorem wholeSpace_exists_lowerOrder_eq {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    {K : NNReal} (hell : UniformlyEllipticOn (Set.univ : Set R3) a lam Lam)
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j))
    {f : Lp ℝ 2 ((volume : Measure R3).restrict ((⊤ : Opens R3) : Set R3))}
    {u : W1p0 (volume : Measure R3) ⊤ 2} (hu : IsWeakSolutionDirichlet a 0 0 f u) :
    ∃ U : Wkp (volume : Measure R3) ⊤ 2 2, Wkp.lowerOrder 1 U = (u : W1p (volume : Measure R3) ⊤ 2) :=
  exists_lowerOrder_eq_var hell hlip hu

end OAI.AnisotropicCalderon.Regularity
