import Calderon.FixedSurfaceFluxIntegration

noncomputable section
namespace OAI.AnisotropicCalderon.FixedSurfaceTransfer

open scoped ContDiff
open OAI.AnisotropicCalderon.FixedSurfaceFlux
open Set MeasureTheory

def spatialPartial (G : R3 → R3 → ℝ) (i : Fin 3) (x y : R3) : ℝ :=
  fderiv ℝ (fun z => G z y) x (coordinateVector i)

def coordinatePartial (f : R3 → ℝ) (x : R3) (i : Fin 3) : ℝ :=
  fderiv ℝ f x (coordinateVector i)

def matrixFlux (A : Coefficients) (f : R3 → ℝ) (x : R3) (i : Fin 3) : ℝ :=
  ∑ j, A x i j * coordinatePartial f x j

def divergence (F : R3 → Fin 3 → ℝ) (x : R3) : ℝ :=
  ∑ i, fderiv ℝ (fun z => F z i) x (coordinateVector i)

def wronskianFlux (A : Coefficients) (u v : R3 → ℝ) (x : R3) (i : Fin 3) : ℝ :=
  v x * matrixFlux A u x i - u x * matrixFlux A v x i

def fluxIntegrand (A : Coefficients) (u : R3 → ℝ) (n : R3 → Fin 3 → ℝ)
    (G : R3 → R3 → ℝ) (x y : R3) : ℝ :=
  ∑ i, (G x y * matrixFlux A u x i -
    u x * matrixFlux A (fun z => G z y) x i) * n x i

def fixedFlux (μ : Measure R3) (A : Coefficients) (u : R3 → ℝ)
    (n : R3 → Fin 3 → ℝ) (G : R3 → R3 → ℝ) (y : R3) : ℝ :=
  ∫ x, fluxIntegrand A u n G x y ∂μ

/-- Primitive data for the Wronskian integral. No regularity or PDE of
its integrand or parameter integral is assumed. The measure and all weights
are fixed in y. -/
structure SmoothFluxData (μ : Measure R3) (K U V : Set R3)
    (A : Coefficients) (u : R3 → ℝ) (n : R3 → Fin 3 → ℝ)
    (G : R3 → R3 → ℝ) : Prop where
  finite_measure : IsFiniteMeasure μ
  compact_support : IsCompact K
  compact_in_domain : K ⊆ U
  open_space_domain : IsOpen U
  open_parameter_domain : IsOpen V
  mass_off_compact : μ Kᶜ = 0
  kernel_smooth : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V)
  matrix_smooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U
  test_smooth : ContDiffOn ℝ ∞ u U
  normal_smooth : ∀ i, ContDiffOn ℝ ∞ (fun x => n x i) U

def SpatialCommutationStatement : Prop :=
  ∀ (U V : Set R3) (G : R3 → R3 → ℝ),
    IsOpen U → IsOpen V → ContDiffOn ℝ 3 (Function.uncurry G) (U ×ˢ V) →
    ∀ (a : Coefficients) (b : R3 → Fin 3 → ℝ) (c : R3 → ℝ),
      ∀ x ∈ U, ∀ i : Fin 3, ∀ y ∈ V,
        secondOrderOperator a b c (spatialPartial G i x) y =
          fderiv ℝ (fun z => secondOrderOperator a b c (G z) y) x (coordinateVector i)

def SpatialHarmonicityStatement : Prop :=
  ∀ (U V : Set R3) (G : R3 → R3 → ℝ),
    IsOpen U → IsOpen V → ContDiffOn ℝ 3 (Function.uncurry G) (U ×ˢ V) →
    ∀ (a : Coefficients) (b : R3 → Fin 3 → ℝ) (c : R3 → ℝ),
      (∀ x ∈ U, ∀ y ∈ V, secondOrderOperator a b c (G x) y = 0) →
      ∀ x ∈ U, ∀ i : Fin 3, ∀ y ∈ V,
        secondOrderOperator a b c (spatialPartial G i x) y = 0

def WronskianDivergenceStatement : Prop :=
  ∀ (U : Set R3) (A : Coefficients) (u v : R3 → ℝ),
    IsOpen U → (∀ i j, ContDiffOn ℝ 1 (fun x => A x i j) U) →
    ContDiffOn ℝ 2 u U → ContDiffOn ℝ 2 v U →
    (∀ x ∈ U, ∀ i j, A x i j = A x j i) →
    ∀ x ∈ U,
      divergence (wronskianFlux A u v) x =
        v x * divergence (matrixFlux A u) x - u x * divergence (matrixFlux A v) x

def FluxIntegrandRegularityStatement : Prop :=
  ∀ (μ : Measure R3) (K U V : Set R3) (A : Coefficients)
    (u : R3 → ℝ) (n : R3 → Fin 3 → ℝ) (G : R3 → R3 → ℝ),
    SmoothFluxData μ K U V A u n G →
      ContDiffOn ℝ 2 (Function.uncurry (fluxIntegrand A u n G)) (U ×ˢ V)

/-- End-to-end parameter analysis for the complete fixed Wronskian flux,
including its regularity and PDE, rather than assuming either for H. -/
def FixedFluxHarmonicityStatement : Prop :=
  ∀ (μ : Measure R3) (K U V : Set R3) (A : Coefficients)
    (u : R3 → ℝ) (n : R3 → Fin 3 → ℝ) (G : R3 → R3 → ℝ),
    SmoothFluxData μ K U V A u n G →
    ∀ (a : Coefficients) (b : R3 → Fin 3 → ℝ) (c : R3 → ℝ),
      (∀ x ∈ U, ∀ y ∈ V, secondOrderOperator a b c (G x) y = 0) →
      ContDiffOn ℝ 2 (fixedFlux μ A u n G) V ∧
        ∀ y ∈ V, secondOrderOperator a b c (fixedFlux μ A u n G) y = 0


open scoped ContDiff
open OAI.AnisotropicCalderon.FixedSurfaceFlux
open Set MeasureTheory Filter Topology

/-! ### Generic calculus helpers -/

lemma natCast_le_infty (k : ℕ) : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast le_top

lemma dAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {s : Set E} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s)
    (hs : IsOpen s) (hn : 1 ≤ n) {p : E} (hp : p ∈ s) : DifferentiableAt ℝ f p :=
  (hf.differentiableOn (lt_of_lt_of_le zero_lt_one hn).ne').differentiableAt (hs.mem_nhds hp)

/-- Directional derivative of a function on the product space. -/
def pd (f : R3 × R3 → ℝ) (d : R3 × R3) : R3 × R3 → ℝ := fun p => fderiv ℝ f p d

lemma pd_contDiffOn {f : R3 × R3 → ℝ} {W : Set (R3 × R3)} {n m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n f W) (hW : IsOpen W) (hmn : m + 1 ≤ n) (d : R3 × R3) :
    ContDiffOn ℝ m (pd f d) W :=
  (hf.fderiv_of_isOpen hW hmn).clm_apply contDiffOn_const

lemma pd_congr {f₁ f₂ : R3 × R3 → ℝ} {p : R3 × R3} (h : f₁ =ᶠ[𝓝 p] f₂) (d : R3 × R3) :
    pd f₁ d p = pd f₂ d p := by
  unfold pd; rw [h.fderiv_eq]

/-- Schwarz symmetry for directional derivatives on the product space. -/
lemma pd_comm {f : R3 × R3 → ℝ} {W : Set (R3 × R3)} {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n f W) (hW : IsOpen W) (hn : 2 ≤ n) {p : R3 × R3} (hp : p ∈ W)
    (d₁ d₂ : R3 × R3) : pd (pd f d₁) d₂ p = pd (pd f d₂) d₁ p := by
  have hsymm := (hf.contDiffAt (hW.mem_nhds hp)).isSymmSndFDerivAt (by simpa using hn)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    dAt (hf.fderiv_of_isOpen hW (m := 1) (by rw [one_add_one_eq_two]; exact hn)) hW le_rfl hp
  unfold pd
  rw [fderiv_clm_apply hd (differentiableAt_const d₁),
    fderiv_clm_apply hd (differentiableAt_const d₂)]
  simp [hsymm d₂ d₁]

/-- First-variable slice derivative as a product-space directional derivative. -/
lemma fderiv_slice_left {h : R3 × R3 → ℝ} {X : R3 → ℝ} {x y : R3}
    (hd : DifferentiableAt ℝ h (x, y)) (heq : X =ᶠ[𝓝 x] fun z => h (z, y)) (v : R3) :
    fderiv ℝ X x v = fderiv ℝ h (x, y) (v, 0) := by
  rw [((hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)).congr_of_eventuallyEq heq).fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- Second-variable slice derivative as a product-space directional derivative. -/
lemma fderiv_slice_right {h : R3 × R3 → ℝ} {Y : R3 → ℝ} {x y : R3}
    (hd : DifferentiableAt ℝ h (x, y)) (heq : Y =ᶠ[𝓝 y] fun z => h (x, z)) (v : R3) :
    fderiv ℝ Y y v = fderiv ℝ h (x, y) (0, v) := by
  rw [((hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).congr_of_eventuallyEq heq).fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-! ### Step 1: commuting an x-derivative past the second-variable operator -/

theorem secondOrder_spatialPartial_commute : SpatialCommutationStatement := by
  intro U V G hU hV hG a b c x hx i y hy
  have hW : IsOpen (U ×ˢ V) := hU.prod hV
  have hxy : (x, y) ∈ U ×ˢ V := ⟨hx, hy⟩
  have g1 : ∀ d, ContDiffOn ℝ 2 (pd (Function.uncurry G) d) (U ×ˢ V) :=
    fun d => pd_contDiffOn hG hW (by norm_num) d
  have g2 : ∀ d d', ContDiffOn ℝ 1 (pd (pd (Function.uncurry G) d) d') (U ×ˢ V) :=
    fun d d' => pd_contDiffOn (g1 d) hW (by norm_num) d'
  have dg : ∀ p ∈ U ×ˢ V, DifferentiableAt ℝ (Function.uncurry G) p :=
    fun p hp => dAt hG hW (by norm_num) hp
  have dg1 : ∀ d, ∀ p ∈ U ×ˢ V, DifferentiableAt ℝ (pd (Function.uncurry G) d) p :=
    fun d p hp => dAt (g1 d) hW (by norm_num) hp
  have dg2 : ∀ d d', ∀ p ∈ U ×ˢ V, DifferentiableAt ℝ (pd (pd (Function.uncurry G) d) d') p :=
    fun d d' p hp => dAt (g2 d d') hW le_rfl hp
  have sx : ∀ z ∈ U, ∀ w ∈ V, ∀ v, fderiv ℝ (fun z' => G z' w) z v =
      pd (Function.uncurry G) (v, 0) (z, w) :=
    fun z hz w hw v => fderiv_slice_left (dg _ ⟨hz, hw⟩) EventuallyEq.rfl v
  have sy : ∀ z ∈ U, ∀ w ∈ V, ∀ v, fderiv ℝ (G z) w v =
      pd (Function.uncurry G) (0, v) (z, w) :=
    fun z hz w hw v => fderiv_slice_right (dg _ ⟨hz, hw⟩) EventuallyEq.rfl v
  -- Schwarz symmetry moves the x-direction to the outside.
  have sym2 : ∀ d, pd (pd (Function.uncurry G) (coordinateVector i, 0)) d (x, y) =
      pd (pd (Function.uncurry G) d) (coordinateVector i, 0) (x, y) :=
    fun d => pd_comm hG hW (by norm_num) hxy _ _
  have sym3 : ∀ d d', pd (pd (pd (Function.uncurry G) (coordinateVector i, 0)) d) d' (x, y) =
      pd (pd (pd (Function.uncurry G) d) d') (coordinateVector i, 0) (x, y) := by
    intro d d'
    have hev : pd (pd (Function.uncurry G) (coordinateVector i, 0)) d =ᶠ[𝓝 (x, y)]
        pd (pd (Function.uncurry G) d) (coordinateVector i, 0) := by
      filter_upwards [hW.mem_nhds hxy] with p hp using pd_comm hG hW (by norm_num) hp _ _
    rw [pd_congr hev]
    exact pd_comm (g1 d) hW le_rfl hxy _ _
  -- The left side.
  have hL0 : ∀ w ∈ V, spatialPartial G i x =ᶠ[𝓝 w]
      fun w' => pd (Function.uncurry G) (coordinateVector i, 0) (x, w') := by
    intro w hw
    filter_upwards [hV.mem_nhds hw] with w' hw' using sx x hx w' hw' _
  have hL00 : spatialPartial G i x y = pd (Function.uncurry G) (coordinateVector i, 0) (x, y) :=
    sx x hx y hy _
  have hL1 : ∀ w ∈ V, ∀ v, fderiv ℝ (spatialPartial G i x) w v =
      pd (pd (Function.uncurry G) (coordinateVector i, 0)) (0, v) (x, w) :=
    fun w hw v => fderiv_slice_right (dg1 _ _ ⟨hx, hw⟩) (hL0 w hw) v
  have hL2 : ∀ k l, fderiv ℝ (fun w => fderiv ℝ (spatialPartial G i x) w (coordinateVector l)) y
      (coordinateVector k) = pd (pd (pd (Function.uncurry G) (coordinateVector i, 0))
        (0, coordinateVector l)) (0, coordinateVector k) (x, y) := by
    intro k l
    refine fderiv_slice_right (dg2 _ _ _ hxy) ?_ _
    filter_upwards [hV.mem_nhds hy] with w hw using hL1 w hw _
  have hLHS : secondOrderOperator a b c (spatialPartial G i x) y =
      (∑ k, ∑ l, a y k l * pd (pd (pd (Function.uncurry G) (0, coordinateVector l))
        (0, coordinateVector k)) (coordinateVector i, 0) (x, y)) +
      (∑ k, b y k * pd (pd (Function.uncurry G) (0, coordinateVector k))
        (coordinateVector i, 0) (x, y)) +
      c y * pd (Function.uncurry G) (coordinateVector i, 0) (x, y) := by
    unfold secondOrderOperator
    simp only [hL2, hL1 y hy, sym3, sym2, hL00]
  -- The right side.
  have hT : HasFDerivAt (fun p : R3 × R3 =>
      (∑ k, ∑ l, a y k l * pd (pd (Function.uncurry G) (0, coordinateVector l))
        (0, coordinateVector k) p) +
      (∑ k, b y k * pd (Function.uncurry G) (0, coordinateVector k) p) +
      c y * Function.uncurry G p)
      ((∑ k, ∑ l, a y k l • fderiv ℝ (pd (pd (Function.uncurry G) (0, coordinateVector l))
        (0, coordinateVector k)) (x, y)) +
      (∑ k, b y k • fderiv ℝ (pd (Function.uncurry G) (0, coordinateVector k)) (x, y)) +
      c y • fderiv ℝ (Function.uncurry G) (x, y)) (x, y) :=
    ((HasFDerivAt.fun_sum fun k _ => HasFDerivAt.fun_sum fun l _ =>
        (dg2 _ _ _ hxy).hasFDerivAt.const_mul (a y k l)).add
      (HasFDerivAt.fun_sum fun k _ => (dg1 _ _ hxy).hasFDerivAt.const_mul (b y k))).add
      ((dg _ hxy).hasFDerivAt.const_mul (c y))
  have hR : (fun z => secondOrderOperator a b c (G z) y) =ᶠ[𝓝 x] fun z =>
      (∑ k, ∑ l, a y k l * pd (pd (Function.uncurry G) (0, coordinateVector l))
        (0, coordinateVector k) (z, y)) +
      (∑ k, b y k * pd (Function.uncurry G) (0, coordinateVector k) (z, y)) +
      c y * Function.uncurry G (z, y) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    have h2 : ∀ k l, fderiv ℝ (fun w => fderiv ℝ (G z) w (coordinateVector l)) y
        (coordinateVector k) = pd (pd (Function.uncurry G) (0, coordinateVector l))
          (0, coordinateVector k) (z, y) := by
      intro k l
      refine fderiv_slice_right (dg1 _ _ ⟨hz, hy⟩) ?_ _
      filter_upwards [hV.mem_nhds hy] with w hw using sy z hz w hw _
    unfold secondOrderOperator
    simp only [h2, sy z hz y hy]
    rfl
  rw [hLHS, hR.fderiv_eq, fderiv_slice_left hT.differentiableAt EventuallyEq.rfl, hT.fderiv]
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul]
  rfl

/-! ### Step 2: x-derivatives of second-variable solutions are solutions -/

theorem secondOrder_spatialPartial_harmonic : SpatialHarmonicityStatement := by
  intro U V G hU hV hG a b c h x hx i y hy
  rw [secondOrder_spatialPartial_commute U V G hU hV hG a b c x hx i y hy]
  have hz : (fun z => secondOrderOperator a b c (G z) y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hx] with z hz using h z hz y hy
  rw [hz.fderiv_eq]
  simp

/-! ### Step 3: variable-coefficient Wronskian divergence identity -/

theorem wronskianFlux_divergence : WronskianDivergenceStatement := by
  intro U A u v hU hA hu hv hsym x hx
  have hxU := hU.mem_nhds hx
  have dA : ∀ i j, DifferentiableAt ℝ (fun z => A z i j) x :=
    fun i j => dAt (hA i j) hU le_rfl hx
  have du : DifferentiableAt ℝ u x := dAt hu hU (by norm_num) hx
  have dv : DifferentiableAt ℝ v x := dAt hv hU (by norm_num) hx
  have dpu : ∀ j, DifferentiableAt ℝ (fun z => coordinatePartial u z j) x := fun j =>
    dAt ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const) hU le_rfl hx
  have dpv : ∀ j, DifferentiableAt ℝ (fun z => coordinatePartial v z j) x := fun j =>
    dAt ((hv.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const) hU le_rfl hx
  have dMu : ∀ i, DifferentiableAt ℝ (fun z => matrixFlux A u z i) x := fun i =>
    DifferentiableAt.fun_sum fun j _ => (dA i j).mul (dpu j)
  have dMv : ∀ i, DifferentiableAt ℝ (fun z => matrixFlux A v z i) x := fun i =>
    DifferentiableAt.fun_sum fun j _ => (dA i j).mul (dpv j)
  have key : ∀ i, fderiv ℝ (fun z => wronskianFlux A u v z i) x (coordinateVector i) =
      v x * fderiv ℝ (fun z => matrixFlux A u z i) x (coordinateVector i) +
        matrixFlux A u x i * coordinatePartial v x i -
      (u x * fderiv ℝ (fun z => matrixFlux A v z i) x (coordinateVector i) +
        matrixFlux A v x i * coordinatePartial u x i) := by
    intro i
    have h1 : HasFDerivAt (fun z => wronskianFlux A u v z i)
        (v x • fderiv ℝ (fun z => matrixFlux A u z i) x + matrixFlux A u x i • fderiv ℝ v x -
          (u x • fderiv ℝ (fun z => matrixFlux A v z i) x +
            matrixFlux A v x i • fderiv ℝ u x)) x :=
      (dv.hasFDerivAt.mul (dMu i).hasFDerivAt).sub (du.hasFDerivAt.mul (dMv i).hasFDerivAt)
    rw [h1.fderiv]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, coordinatePartial]
  -- The cross-gradient bilinear forms cancel by symmetry of A.
  have hcross : ∑ i, (matrixFlux A u x i * coordinatePartial v x i -
      matrixFlux A v x i * coordinatePartial u x i) = 0 := by
    simp only [matrixFlux, Finset.sum_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym x hx j i]
    ring
  unfold divergence
  simp only [key]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← sub_eq_zero,
    ← Finset.sum_sub_distrib, ← hcross]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Step 4: joint regularity of the complete flux integrand -/

lemma flux_integrand_contDiffOn {μ : Measure R3} {K U V : Set R3} {A : Coefficients}
    {u : R3 → ℝ} {n : R3 → Fin 3 → ℝ} {G : R3 → R3 → ℝ}
    (D : SmoothFluxData μ K U V A u n G) (m : ℕ) :
    ContDiffOn ℝ m (Function.uncurry (fluxIntegrand A u n G)) (U ×ˢ V) := by
  have hU := D.open_space_domain
  have hW : IsOpen (U ×ˢ V) := hU.prod D.open_parameter_domain
  have hG : ContDiffOn ℝ (m + 1 : ℕ) (Function.uncurry G) (U ×ˢ V) :=
    D.kernel_smooth.of_le (natCast_le_infty _)
  have hfst : ∀ f : R3 → ℝ, ContDiffOn ℝ m f U →
      ContDiffOn ℝ m (fun p : R3 × R3 => f p.1) (U ×ˢ V) :=
    fun f hf => hf.comp contDiff_fst.contDiffOn fun p hp => hp.1
  have hA : ∀ i j, ContDiffOn ℝ m (fun p : R3 × R3 => A p.1 i j) (U ×ˢ V) :=
    fun i j => hfst _ ((D.matrix_smooth i j).of_le (natCast_le_infty _))
  have hu : ContDiffOn ℝ m (fun p : R3 × R3 => u p.1) (U ×ˢ V) :=
    hfst _ (D.test_smooth.of_le (natCast_le_infty _))
  have hn : ∀ i, ContDiffOn ℝ m (fun p : R3 × R3 => n p.1 i) (U ×ˢ V) :=
    fun i => hfst _ ((D.normal_smooth i).of_le (natCast_le_infty _))
  have hdu : ∀ j, ContDiffOn ℝ m (fun p : R3 × R3 => coordinatePartial u p.1 j) (U ×ˢ V) :=
    fun j => hfst _ (((D.test_smooth.of_le (natCast_le_infty (m + 1))).fderiv_of_isOpen hU
      (Nat.cast_succ m).ge).clm_apply contDiffOn_const)
  have hdG : ∀ j, ContDiffOn ℝ m
      (fun p : R3 × R3 => coordinatePartial (fun z => G z p.2) p.1 j) (U ×ˢ V) := by
    intro j
    refine (pd_contDiffOn hG hW (Nat.cast_succ m).ge (coordinateVector j, 0)).congr ?_
    rintro ⟨z, w⟩ hp
    show coordinatePartial (fun z' => G z' w) z j =
      pd (Function.uncurry G) (coordinateVector j, 0) (z, w)
    exact fderiv_slice_left
      (dAt D.kernel_smooth hW (le_trans (by simp) (natCast_le_infty 1)) hp) EventuallyEq.rfl _
  have hGm : ContDiffOn ℝ m (Function.uncurry G) (U ×ˢ V) :=
    hG.of_le (Nat.cast_le.2 (Nat.le_succ m))
  show ContDiffOn ℝ m (fun p : R3 × R3 => ∑ i, (Function.uncurry G p *
      ∑ j, A p.1 i j * coordinatePartial u p.1 j -
      u p.1 * ∑ j, A p.1 i j * coordinatePartial (fun z => G z p.2) p.1 j) * n p.1 i) (U ×ˢ V)
  exact ContDiffOn.sum fun i _ => ((hGm.mul (ContDiffOn.sum fun j _ => (hA i j).mul (hdu j))).sub
    (hu.mul (ContDiffOn.sum fun j _ => (hA i j).mul (hdG j)))).mul (hn i)

theorem fixedFlux_integrand_C2 : FluxIntegrandRegularityStatement := by
  intro μ K U V A u n G D
  exact flux_integrand_contDiffOn D 2

/-! ### Step 5 helpers: parameter-integral regularity -/

/-- A fixed compactly carried finite-measure integral of a jointly `C^(k+1)` kernel is
`C^k` in the parameter, proved by iterating differentiation under the integral sign. -/
lemma contDiffOn_parametric_integral {μ : Measure R3} [IsFiniteMeasure μ] {K U V : Set R3}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    (k : ℕ) : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : R3 → R3 → E),
      ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) (U ×ˢ V) →
      ContDiffOn ℝ (k : WithTop ℕ∞) (fun z => ∫ x, f x z ∂μ) V := by
  induction k with
  | zero =>
    intro E _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    intro y hy
    exact (hasFDerivAt_integral hK hKU hU hV hμ hf (by simp) hy).continuousAt.continuousWithinAt
  | succ k ih =>
    intro E _ _ f hf
    have h1 : (1 : WithTop ℕ∞) ≤ ((k + 1 + 1 : ℕ) : WithTop ℕ∞) :=
      le_trans (by simp) (Nat.cast_le.2 (by omega : 1 ≤ k + 1 + 1))
    have hf' := contDiffOn_partial hf (n := ((k + 1 : ℕ) : WithTop ℕ∞))
      (Nat.cast_succ (k + 1)).ge hU hV
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hV]
    refine ⟨fun y hy =>
      (hasFDerivAt_integral hK hKU hU hV hμ hf h1 hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine (ih _ hf').congr fun y hy => ?_
    exact (hasFDerivAt_integral hK hKU hU hV hμ hf h1 hy).fderiv

/-! ### Step 5 helpers: linearity of the second-variable operator -/

/-- `f` is `C²` on `V` and solves the second-order equation there. -/
def SolvesOn (a : Coefficients) (b : R3 → Fin 3 → ℝ) (c : R3 → ℝ) (V : Set R3)
    (f : R3 → ℝ) : Prop :=
  ContDiffOn ℝ 2 f V ∧ ∀ y ∈ V, secondOrderOperator a b c f y = 0

section Linearity
variable {a : Coefficients} {b : R3 → Fin 3 → ℝ} {c : R3 → ℝ} {V : Set R3}

lemma differentiableAt_coordPartial (hV : IsOpen V) {f : R3 → ℝ} (hf : ContDiffOn ℝ 2 f V)
    (j : Fin 3) {y : R3} (hy : y ∈ V) :
    DifferentiableAt ℝ (fun z => fderiv ℝ f z (coordinateVector j)) y :=
  dAt ((hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const) hV le_rfl hy

lemma secondOrder_add (hV : IsOpen V) {f g : R3 → ℝ} (hf : ContDiffOn ℝ 2 f V)
    (hg : ContDiffOn ℝ 2 g V) {y : R3} (hy : y ∈ V) :
    secondOrderOperator a b c (fun z => f z + g z) y =
      secondOrderOperator a b c f y + secondOrderOperator a b c g y := by
  have h1 : ∀ z ∈ V, fderiv ℝ (fun w => f w + g w) z = fderiv ℝ f z + fderiv ℝ g z :=
    fun z hz => fderiv_fun_add (dAt hf hV (by norm_num) hz) (dAt hg hV (by norm_num) hz)
  have h3 : ∀ i j, fderiv ℝ (fun z => fderiv ℝ (fun w => f w + g w) z (coordinateVector j)) y
      (coordinateVector i) =
      fderiv ℝ (fun z => fderiv ℝ f z (coordinateVector j)) y (coordinateVector i) +
      fderiv ℝ (fun z => fderiv ℝ g z (coordinateVector j)) y (coordinateVector i) := by
    intro i j
    have h2 : (fun z => fderiv ℝ (fun w => f w + g w) z (coordinateVector j)) =ᶠ[𝓝 y]
        fun z => fderiv ℝ f z (coordinateVector j) + fderiv ℝ g z (coordinateVector j) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [h1 z hz]; rfl
    rw [h2.fderiv_eq, fderiv_fun_add (differentiableAt_coordPartial hV hf j hy)
      (differentiableAt_coordPartial hV hg j hy)]
    rfl
  have h4 : ∀ i, fderiv ℝ (fun w => f w + g w) y (coordinateVector i) =
      fderiv ℝ f y (coordinateVector i) + fderiv ℝ g y (coordinateVector i) := by
    intro i; rw [h1 y hy]; rfl
  unfold secondOrderOperator
  simp only [h3, h4, mul_add, Finset.sum_add_distrib]
  ring

lemma secondOrder_const_mul (hV : IsOpen V) {f : R3 → ℝ} (hf : ContDiffOn ℝ 2 f V) (r : ℝ)
    {y : R3} (hy : y ∈ V) :
    secondOrderOperator a b c (fun z => r * f z) y = r * secondOrderOperator a b c f y := by
  have h1 : ∀ z ∈ V, fderiv ℝ (fun w => r * f w) z = r • fderiv ℝ f z :=
    fun z hz => fderiv_const_mul (dAt hf hV (by norm_num) hz) r
  have h3 : ∀ i j, fderiv ℝ (fun z => fderiv ℝ (fun w => r * f w) z (coordinateVector j)) y
      (coordinateVector i) =
      r * fderiv ℝ (fun z => fderiv ℝ f z (coordinateVector j)) y (coordinateVector i) := by
    intro i j
    have h2 : (fun z => fderiv ℝ (fun w => r * f w) z (coordinateVector j)) =ᶠ[𝓝 y]
        fun z => r * fderiv ℝ f z (coordinateVector j) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [h1 z hz]; rfl
    rw [h2.fderiv_eq, fderiv_const_mul (differentiableAt_coordPartial hV hf j hy)]
    rfl
  have h4 : ∀ i, fderiv ℝ (fun w => r * f w) y (coordinateVector i) =
      r * fderiv ℝ f y (coordinateVector i) := by
    intro i; rw [h1 y hy]; rfl
  unfold secondOrderOperator
  simp only [h3, h4, Finset.mul_sum, mul_add, mul_left_comm _ r]

lemma solvesOn_add (hV : IsOpen V) {f g : R3 → ℝ} (hf : SolvesOn a b c V f)
    (hg : SolvesOn a b c V g) : SolvesOn a b c V (fun z => f z + g z) :=
  ⟨hf.1.add hg.1, fun y hy => by
    rw [secondOrder_add hV hf.1 hg.1 hy, hf.2 y hy, hg.2 y hy, add_zero]⟩

lemma solvesOn_const_mul (hV : IsOpen V) (r : ℝ) {f : R3 → ℝ} (hf : SolvesOn a b c V f) :
    SolvesOn a b c V (fun z => r * f z) :=
  ⟨contDiffOn_const.mul hf.1, fun y hy => by
    rw [secondOrder_const_mul hV hf.1 r hy, hf.2 y hy, mul_zero]⟩

lemma solvesOn_mul_const (hV : IsOpen V) (r : ℝ) {f : R3 → ℝ} (hf : SolvesOn a b c V f) :
    SolvesOn a b c V (fun z => f z * r) := by
  have h : (fun z => f z * r) = fun z => r * f z := funext fun z => mul_comm _ _
  rw [h]
  exact solvesOn_const_mul hV r hf

lemma solvesOn_sub (hV : IsOpen V) {f g : R3 → ℝ} (hf : SolvesOn a b c V f)
    (hg : SolvesOn a b c V g) : SolvesOn a b c V (fun z => f z - g z) := by
  have h : (fun z => f z - g z) = fun z => f z + (-1) * g z := funext fun z => by ring
  rw [h]
  exact solvesOn_add hV hf (solvesOn_const_mul hV (-1) hg)

lemma solvesOn_sum (hV : IsOpen V) {ι : Type*} (s : Finset ι) (F : ι → R3 → ℝ)
    (h : ∀ i ∈ s, SolvesOn a b c V (F i)) : SolvesOn a b c V (fun z => ∑ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨contDiffOn_const, fun y _ => by simp [secondOrderOperator]⟩
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact solvesOn_add hV (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Linearity

/-! ### Step 5: regularity and PDE of the complete fixed flux -/

theorem fixedFlux_C2_and_harmonic : FixedFluxHarmonicityStatement := by
  intro μ K U V A u n G D a b c hL
  have := D.finite_measure
  have hK := D.compact_support
  have hKU := D.compact_in_domain
  have hU := D.open_space_domain
  have hV := D.open_parameter_domain
  have hμ := D.mass_off_compact
  have hW : IsOpen (U ×ˢ V) := hU.prod hV
  have hG3 : ContDiffOn ℝ 3 (Function.uncurry G) (U ×ˢ V) :=
    D.kernel_smooth.of_le (natCast_le_infty 3)
  have FD : FixedSurfaceData μ K U V (fluxIntegrand A u n G) :=
    ⟨D.finite_measure, hK, hKU, hU, hV, hμ, flux_integrand_contDiffOn D 2⟩
  refine ⟨contDiffOn_parametric_integral hK hKU hU hV hμ 2 _ (flux_integrand_contDiffOn D (2 + 1)),
    ?_⟩
  have hsol : ∀ x ∈ U, SolvesOn a b c V (fluxIntegrand A u n G x) := by
    intro x hx
    have hGx : SolvesOn a b c V (G x) :=
      ⟨(hG3.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun y hy => ⟨hx, hy⟩), fun y hy => hL x hx y hy⟩
    have hSp : ∀ j, SolvesOn a b c V (spatialPartial G j x) := by
      intro j
      refine ⟨?_, fun y hy => secondOrder_spatialPartial_harmonic U V G hU hV hG3 a b c hL
        x hx j y hy⟩
      refine ((pd_contDiffOn hG3 hW (m := 2) (by norm_num) (coordinateVector j, 0)).comp
        (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨hx, hy⟩)).congr
        fun y hy => ?_
      exact fderiv_slice_left (dAt hG3 hW (by norm_num) ⟨hx, hy⟩) EventuallyEq.rfl _
    show SolvesOn a b c V (fun y => ∑ i, (G x y * matrixFlux A u x i -
      u x * ∑ j, A x i j * spatialPartial G j x y) * n x i)
    refine solvesOn_sum hV Finset.univ (fun i y => (G x y * matrixFlux A u x i -
      u x * ∑ j, A x i j * spatialPartial G j x y) * n x i) fun i _ => ?_
    refine solvesOn_mul_const hV (n x i) (f := fun y => G x y * matrixFlux A u x i -
      u x * ∑ j, A x i j * spatialPartial G j x y) ?_
    refine solvesOn_sub hV (f := fun y => G x y * matrixFlux A u x i)
      (g := fun y => u x * ∑ j, A x i j * spatialPartial G j x y) ?_ ?_
    · exact solvesOn_mul_const hV _ hGx
    · refine solvesOn_const_mul hV (u x) (f := fun y => ∑ j, A x i j * spatialPartial G j x y) ?_
      exact solvesOn_sum hV Finset.univ (fun j y => A x i j * spatialPartial G j x y)
        fun j _ => solvesOn_const_mul hV _ (hSp j)
  intro y hy
  exact integral_secondOrder_harmonic μ K U V _ FD a b c
    (fun x hx z hz => (hsol x (hKU hx)).2 z hz) y hy


end OAI.AnisotropicCalderon.FixedSurfaceTransfer
