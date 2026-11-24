module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct

/-! # The spectral trace statements of §10.4.2 at orders between zero and one -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "H₀" => spectralSobolevQuotient F a hI hs
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs φ
local notation "Aq(" φ ")" => spectralConvolution (F := F) a hI hs φ
local notation "M(" hc ")" => modulatedCutoffOperator m𝔽
  ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logIdeleClassNorm F g))) hc
local notation "band(" R ", " ε ")" => (0 < (R : ℝ)⁻¹ + ε ∧ R⁻¹ + ε < R - ε)

variable {Λ ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). On a strip of width zero
at order at most one, quotient convolution is nuclear.
Deviation: This special case uses the density of theta at the strict endpoint cutoff of §10.2. -/
theorem spectralStripConvolution_nuclear_of_zero_width (hwidth : α = 0) (hs₁ : s ≤ 1)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  subst α
  have line (l : ℝ) (hl : l ≤ 0) (heq : l = 0) :
      IsNuclearOperator (E := spectralSobolevQuotient F a hl hs) (F := spectralSobolevQuotient F a hl hs)
        (spectralConvolution (F := F) a hl hs φ) := by
    subst l
    have hz (q : spectralSobolevQuotient F a hl hs) : q = 0 := by
      obtain ⟨v, rfl⟩ := (globalThetaSobolev F a hl hs).mkQ_surjective q
      apply (spectralSobolevQuotient_eq_zero a hl hs v).2
      rw [globalThetaSobolev_line_eq_top_of_le_one (F := F) a s hs hs₁]
      exact Submodule.mem_top
    have hA : spectralConvolution (F := F) a hl hs φ = 0 :=
      ContinuousLinearMap.ext fun _ ↦ hz _
    rw [hA]
    exact (nuclearEndomorphisms _).zero_mem
  exact line (-0) ((neg_nonpos.mpr hα).trans hα) neg_zero

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Every compactly supported
Bruhat test acts by a nuclear convolution operator on the strip quotient.
Deviation: The theorems of §10.4.2 print `s ≥ 0`, while p. 455 assumes `s > 1` for
the section. This statement covers `0 ≤ s ≤ 1`.
Gap: The strip theorem 10.3.2.1 requires `s > 1`. At the orders considered here,
`spectralStripConvolution_nuclear_of_zero_width` settles width zero, leaving nuclearity
open for positive width. Nothing in the Lean uses this statement, and it is not known how
it connects with the rest of the proof in Lean; in the paper it is used on pp. 459–461,
463–464, 503, 519–520. -/
theorem spectralStripConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  sorry

/-- Classical input: the Dixmier–Malliavin factorization theorem, J. Dixmier and P. Malliavin,
*Factorisations de fonctions et de vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2)
102 (1978), no. 4, 307–330, Théorème 3.1: for a Lie group `L`, every function in `C_c^∞(L)` is a
finite sum of convolutions of two functions in `C_c^∞(L)`. Here it is applied to the idele class
group, for the Tamagawa Haar measure. A compactly supported Bruhat test is invariant under a good
subgroup `K` (a compact subgroup of the finite idele classes) and descends to a smooth compactly
supported function on the Lie group `C_F / K` (F. Bruhat, *Distributions sur un groupe localement
compact et applications à l'étude des représentations des groupes p-adiques*, Bull. Soc. Math.
France 89 (1961), 43–75). Factor it there and pull the factors back; convolution on `C_F` of
`K`-invariant functions is convolution on `C_F / K` up to the volume of `K`, which is absorbed into
one factor. The real-line case is `spectralHomogeneousTest_real_factorization` in
`Ch10_TraceSpectral/Sec3.lean`. -/
theorem bruhatCompactSupport_mem_closure_convolution (φ : BruhatCompactSupport C𝔽) :
    φ ∈ AddSubmonoid.closure {h : BruhatCompactSupport C𝔽 |
      ∃ u v : BruhatCompactSupport C𝔽, h.val = lcaConvolution μ𝔽 u.val v.val} := by
  sorry

/-- Spectral convolution by a convolution of two tests is the composite of the two spectral
convolutions. -/
private theorem spectralStripConvolution_nuclear_of_hilbertSchmidt_comp
    (t u v : BruhatCompactSupport C𝔽) (ht : t.val = lcaConvolution μ𝔽 u.val v.val) :
    Aq(t) = (Aq(u)).comp (Aq(v)) := by
  let ρ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs
  have hρ := (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs).choose_spec.2
  obtain ⟨θ, hθ, hact⟩ := bruhatRegularizedAction_convolution μ𝔽 ρ hρ u v
  have heq : θ = t := Subtype.ext (hθ.trans ht.symm)
  subst heq
  ext q
  obtain ⟨w, rfl⟩ := (globalThetaSobolev F a hI hs).mkQ_surjective q
  rw [ContinuousLinearMap.comp_apply, spectralConvolution_mkQ, spectralConvolution_mkQ,
    spectralConvolution_mkQ]
  exact congrArg _ (hact w)

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). If every test acts on the strip
quotient by a Hilbert–Schmidt operator, then every test acts by a nuclear operator.
Reconstruction: The paper does not state a Hilbert–Schmidt bound; this is a sufficient condition
for `spectralStripConvolution_nuclear_of_le_one`, proved from the classical input
`bruhatCompactSupport_mem_closure_convolution`: a test is a finite sum of convolutions `u * v`,
the quotient action takes `u * v` to the composite of the two actions, and a composite of two
Hilbert–Schmidt operators is nuclear (`nuclear_hilbertSchmidt_comp`).
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_of_hilbertSchmidt
    (hHS : ∀ ψ : BruhatCompactSupport C𝔽, Aq(ψ) ∈ hilbertSchmidtOperators H₀ H₀)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  induction (bruhatCompactSupport_mem_closure_convolution φ) using
    AddSubmonoid.closure_induction with
  | mem h hh =>
    obtain ⟨u, v, huv⟩ := hh
    rw [spectralStripConvolution_nuclear_of_hilbertSchmidt_comp a hα hs h u v huv]
    exact nuclear_hilbertSchmidt_comp ⟨_, hHS u⟩ ⟨_, hHS v⟩
  | zero =>
    rw [(spectralConvolution_isLinear (F := F) a hI hs).map_zero]
    exact (nuclearEndomorphisms _).zero_mem
  | add x y _ _ hx hy =>
    rw [(spectralConvolution_isLinear (F := F) a hI hs).map_add]
    exact (nuclearEndomorphisms _).add_mem hx hy

/-- Summable real sequences are square summable. -/
private theorem spectralStripConvolution_hilbertSchmidt_of_nuclear_summable (f : ℕ → ℝ)
    (hf : Summable (fun n ↦ f n ^ (1 : ℝ))) : Summable (fun n ↦ f n ^ (2 : ℝ)) := by
  simp only [Real.rpow_one] at hf
  simp only [Real.rpow_two]
  have h0 : ∀ᶠ n in cofinite, ‖f n‖ ≤ 1 := by
    have := (hf.tendsto_cofinite_zero).norm
    rw [norm_zero] at this
    exact this.eventually (eventually_le_nhds one_pos)
  refine hf.norm.of_norm_bounded_eventually ?_
  filter_upwards [h0] with n hn
  rw [norm_pow, sq]
  exact mul_le_of_le_one_left (norm_nonneg _) hn

/-- Paper: Theorem 10.4.2.1, p. 459. A nuclear quotient convolution is Hilbert–Schmidt: the
converse of `spectralStripConvolution_nuclear_of_hilbertSchmidt`, test by test. -/
theorem spectralStripConvolution_hilbertSchmidt_of_nuclear (φ : BruhatCompactSupport C𝔽)
    (hn : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) :
    Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ := by
  obtain ⟨hc, hsum⟩ := (mem_traceClassOperators_iff_isNuclearOperator _).mpr hn
  exact ⟨hc, spectralStripConvolution_hilbertSchmidt_of_nuclear_summable _ hsum⟩

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). At each order and width, every test
acts on the strip quotient by a nuclear operator exactly when every test acts by a
Hilbert–Schmidt operator. So the conclusion of `spectralStripConvolution_nuclear_of_le_one`
is equivalent to the Hilbert–Schmidt property, given the classical input
`bruhatCompactSupport_mem_closure_convolution`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_iff_hilbertSchmidt :
    (∀ φ : BruhatCompactSupport C𝔽, IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) ↔
      ∀ φ : BruhatCompactSupport C𝔽, Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ :=
  ⟨fun h φ ↦ spectralStripConvolution_hilbertSchmidt_of_nuclear a hα hs φ (h φ),
    fun h φ ↦ spectralStripConvolution_nuclear_of_hilbertSchmidt a hα hs h φ⟩

/-- Approximation numbers are nonnegative. -/
private theorem spectralStripConvolution_hilbertSchmidt_of_spectralProjection_nonneg
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (T : E →L[ℂ] G) (n : ℕ) :
    0 ≤ approximationNumber T n :=
  Real.sInf_nonneg (by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _)

/-- Composing a Hilbert–Schmidt operator with bounded operators on both sides gives a
Hilbert–Schmidt operator. -/
private theorem spectralStripConvolution_hilbertSchmidt_of_spectralProjection_ideal
    {D E G K : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [CompleteSpace D] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (L : G →L[ℂ] K) (X : E →L[ℂ] G) (R : D →L[ℂ] E) (hX : X ∈ hilbertSchmidtOperators E G) :
    (L.comp X).comp R ∈ hilbertSchmidtOperators D K := by
  obtain ⟨hc, hsum⟩ := hX
  refine ⟨(hc.clm_comp L).comp_clm R, ?_⟩
  simp only [Real.rpow_two] at hsum ⊢
  set c := approximationNumber L 0 * approximationNumber R 0
  have hb (n : ℕ) :
      approximationNumber ((L.comp X).comp R) (n + 2) ≤ c * approximationNumber X n := by
    have h1 := approximationNumber_comp_le (L.comp X) R (n + 1) 0
    have h2 := approximationNumber_comp_le L X 0 n
    have e1 : n + 1 + 0 + 1 = n + 2 := by omega
    have e2 : 0 + n + 1 = n + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    calc _ ≤ approximationNumber (L.comp X) (n + 1) * approximationNumber R 0 := h1
      _ ≤ (approximationNumber L 0 * approximationNumber X n) * approximationNumber R 0 :=
          mul_le_mul_of_nonneg_right h2
            (spectralStripConvolution_hilbertSchmidt_of_spectralProjection_nonneg _ _)
      _ = c * approximationNumber X n := by ring
  refine (summable_nat_add_iff 2).mp ?_
  refine (hsum.mul_left (c ^ 2)).of_nonneg_of_le (fun n ↦ sq_nonneg _) (fun n ↦ ?_)
  rw [← mul_pow]
  exact pow_le_pow_left₀
    (spectralStripConvolution_hilbertSchmidt_of_spectralProjection_nonneg _ _) (hb n) 2

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). If convolution after spectral
projection is Hilbert–Schmidt on the weighted space, then quotient convolution is
Hilbert–Schmidt.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This reduces the hypothesis
of `spectralStripConvolution_nuclear_of_hilbertSchmidt` to a statement on the weighted space:
the quotient action is the quotient map after convolution after spectral projection, applied
to the isometric section of the quotient map, and Hilbert–Schmidt operators form an ideal.
For a Hilbert basis `e` of the spectral complement, the hypothesis says that the sum of
`‖A(φ) e n‖²` is finite. The converse would also need the block from the spectral complement
to the theta subspace to be Hilbert–Schmidt, which this argument does not give.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_hilbertSchmidt_of_spectralProjection (φ : BruhatCompactSupport C𝔽)
    (hHS : (A(φ)).comp (spectralProjection (F := F) a hα hs) ∈ hilbertSchmidtOperators W W) :
    Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ := by
  let Θ := globalThetaSobolev F a hI hs
  let S : H₀ →L[ℂ] W := Θᗮ.subtypeL.comp
    Θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hS (x : H₀) : Θ.mkQ (S x) = x ∧ spectralProjection (F := F) a hα hs (S x) = S x :=
    ⟨by simp [S], Submodule.starProjection_eq_self_iff.mpr (Θ.quotientEquivOrthogonal x).2⟩
  have heq : Aq(φ) = (Θ.mkQL.comp ((A(φ)).comp (spectralProjection (F := F) a hα hs))).comp S := by
    ext x
    obtain ⟨h1, h2⟩ := hS x
    conv_lhs => rw [← h1]
    rw [spectralConvolution_mkQ]
    change _ = Θ.mkQ (A(φ) (spectralProjection (F := F) a hα hs (S x)))
    rw [h2]
  rw [heq]
  exact spectralStripConvolution_hilbertSchmidt_of_spectralProjection_ideal _ _ _ hHS

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). If convolution after spectral
projection is Hilbert–Schmidt on the weighted space for every test, then every test acts on the
strip quotient by a nuclear operator.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This combines
`spectralStripConvolution_hilbertSchmidt_of_spectralProjection` with
`spectralStripConvolution_nuclear_of_hilbertSchmidt`, and so uses the classical input
`bruhatCompactSupport_mem_closure_convolution`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_of_spectralProjection_hilbertSchmidt
    (hHS : ∀ ψ : BruhatCompactSupport C𝔽,
      (A(ψ)).comp (spectralProjection (F := F) a hα hs) ∈ hilbertSchmidtOperators W W)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) :=
  spectralStripConvolution_nuclear_of_hilbertSchmidt a hα hs
    (fun ψ ↦ spectralStripConvolution_hilbertSchmidt_of_spectralProjection a hα hs ψ (hHS ψ)) φ

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
This follows from the open statement `spectralStripConvolution_nuclear_of_le_one` by (10.4.2.5).
Deviation: This is the part of the printed range with `0 ≤ s ≤ 1`. The operator is independent
of the cutoff. -/
theorem spectralProjection_convolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  spectralProjection_convolution_nuclear a hα hs φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
Deviation: This checks the uncut conclusion on the range `1 < s` of the strip theorem. -/
theorem spectralProjection_convolution_nuclear_of_one_lt (hs₁ : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  RiemannMasullo.spectralProjection_convolution_nuclear_of_one_lt a hα hs₁ φ

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, spectral truncation
after convolution is nuclear. This follows from the open `spectralStripConvolution_nuclear_of_le_one`
by composing the projected convolution with cutoff multiplication.
Deviation: The range here is `0 ≤ s ≤ 1`. The real cutoff uses the profile of Definition 9.3.3.1. -/
theorem spectralTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  spectralTruncatedConvolution_nuclear a hα hs hρ φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral truncation after convolution is nuclear.
Deviation: At `1 < s` the existing theorem applies to real cutoffs even without the inner-band inequality. -/
theorem spectralTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.spectralTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ φ

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, geometric truncation
after convolution is nuclear. Given the open `spectralStripConvolution_nuclear_of_le_one`,
this follows by subtracting the spectral summand from cutoff convolution.
Deviation: The range here is `0 ≤ s ≤ 1`, with the real cutoff of Definition 9.3.3.1. -/
theorem geometricTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  geometricTruncatedConvolution_nuclear a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Geometric truncation after convolution is nuclear.
Deviation: This checks the real-cutoff conclusion at `1 < s` using the strip theorem. -/
theorem geometricTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.geometricTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ hband φ

local notation "traceSplit(" hρ ", " φ ")" =>
  (let T := (M(hρ)).comp (A(φ))
   let G := geometricTruncatedConvolution a hα hs hρ φ
   let S := spectralTruncatedConvolution a hα hs hρ φ
   ∃ (hT : IsNuclearOperator T) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S),
     hilbertTrace (H := W) ⟨T, hT⟩ =
       hilbertTrace (H := W) ⟨G, hG⟩ + hilbertTrace (H := W) ⟨S, hS⟩)

/-- Paper: Theorem 10.4.2.1, p. 459. At an admissible cutoff the trace of cutoff convolution
is the sum of the geometric and spectral traces, as in (10.4.2.3). The open statement
`spectralStripConvolution_nuclear_of_le_one` supplies the hypothesis for the trace split.
Deviation: The order is restricted to `0 ≤ s ≤ 1` and the three nuclearity witnesses are
part of the conclusion for the real cutoff. -/
theorem truncatedConvolution_trace_split_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  truncatedConvolution_trace_split a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. The nuclear trace splits as in (10.4.2.3).
Deviation: This checks the identity with real cutoffs and all three nuclearity witnesses at `1 < s`. -/
theorem truncatedConvolution_trace_split_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  RiemannMasullo.truncatedConvolution_trace_split_of_one_lt a hα hs₁ hρ hband φ

section Limits

variable (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ε : ℝ → ℝ)
  (ρ : ℝ → IdeleClassGroup (𝓞 F) F → ℝ)

local notation "traceLimit(" op ")" =>
  (∃ (hq : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) (t : ℝ → ℂ),
    (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
      let T := (op) a hα hs hc φ
      ∃ hT : IsNuclearOperator T, t R = hilbertTrace (H := W) ⟨T, hT⟩) ∧
    Tendsto t atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aq(φ), hq⟩)))

variable (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
  (hρ : ∀ᶠ R in atTop, IsModulatedCutoff (continuousIdeleClassNorm F) R (ε R) (ρ R) ∧ band(R, ε R))

include hε hρ

/-- Paper: Theorem 10.4.2.2, p. 460. The traces of cutoff projection after convolution tend
to the trace of convolution on the strip quotient, as in (10.4.2.9). This follows from
the open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The proof
on p. 461 uses the strip quotient. Real cutoffs and their traces need only agree with the
prescribed data eventually as the radius tends to infinity. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralTruncatedConvolution) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralTruncatedConvolution_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.2, p. 460. The projection-after-convolution traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralTruncatedConvolution) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralTruncatedConvolution_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The traces of cutoff convolution after spectral
projection tend to the strip quotient trace, as in (10.4.2.20). This follows from the
open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The real
cutoff conditions and agreement with the nuclear traces are eventual. -/
theorem spectralRestriction_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralRestriction) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralRestriction_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The convolution-after-projection traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralRestriction_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralRestriction) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralRestriction_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

end Limits

end RiemannMasullo.Isolated
