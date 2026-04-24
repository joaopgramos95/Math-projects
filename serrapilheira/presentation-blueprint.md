# Presentation Blueprint

## Working Goal

Build a short deck in Bruno Braga's style: calm, sparse, legible, and progressive. The talk should feel like a clean narrative:

1. who you are,
2. what you have done,
3. the big question,
4. why it matters,
5. what the conjecture is,
6. why this project is bold and timely.

Target length: 9 frames, with overlays inside frames.

## Style Cues From Braga's Deck

- White background, dark green titles, very light green accent bands/boxes.
- Large type and generous whitespace.
- One idea per frame.
- Use overlays to reveal bullets one at a time.
- Keep text short on screen; let the spoken explanation carry the detail.
- Pictures/diagrams should anchor imagination, not decorate.
- Avoid dense formulas in the main deck. If one formula appears, keep it small and subordinate.

Wave-themed variant that still fits Braga's tone:

- Keep the same light green palette, but use a very subtle wave motif in one or two places only.
- Good accents: thin sinusoidal line, faint ripple, or a sparse sampling diagram.
- Do not turn the slides into a themed poster; keep the visual language restrained.

## Recommended Arc

### Frame 1. Title

**Draft title**

How much information is needed to reconstruct a wave?

**Subtitle**

Sparse observations, Fourier intuition, and Schrodinger evolution

**Visual suggestion**

- Rounded light-green title box, like Braga's title slide.
- Very faint wave line or ripple pattern near the bottom.

**Speaker goal**

State the whole talk in one sentence: the project asks whether a wave can be determined from surprisingly little discrete information.

---

### Frame 2. My path so far

Use Braga's `Where have I been?` rhythm and reveal one item at a time.

**On-screen draft**

My path so far

- Undergraduate and master's: [fill in]
- PhD / postdoc stages: [fill in]
- Current position: IMPA

**Visual suggestion**

- Institution logos or a simple geographic path.
- Keep the slide mostly empty; do not crowd it.

**Note**

If you want to match Braga closely, make this frame mostly text and let the institutions appear progressively.

---

### Frame 3. My work so far

Start with the fields, then reveal the highlights.

**On-screen draft**

My work so far

- Harmonic analysis
- Partial differential equations
- Probability theory

Selected highlights:

- Concentration for STFT (`Inventiones`)
- Interpolation formulas and Fourier uniqueness (`JEMS`, `Analysis & PDE`, `Annals of PDE`)
- Stability for sphere packings in dimensions 8 and 24 (`Crelle`)

**Visual suggestion**

- Three-lane diagram converging to a central node: `reconstruction of waves`.
- Alternative: three short labeled bands with one key paper/result under each.

**Speaker goal**

Show that your past work naturally leads into the proposed project rather than looking like a jump.

---

### Frame 4. The big question

This should be the emotional and conceptual center of the talk.

**On-screen draft**

The big question

How much information is enough to determine a wave?

- We almost never observe a whole system.
- We only see scattered measurements in space and time.
- Can sparse data still determine the full evolution?

**Picture suggestions**

- Water ripples seen from above.
- A spectrogram or audio waveform.
- Ocean buoys / radar / MRI / seismic sampling.
- A pop-culture adjacent option: a guitar string plus its waveform or spectrogram.

**Speaker goal**

Make the question feel universal before making it technical.

---

### Frame 5. Why should this be true?

This is the motivation frame. Keep it clean and intuitive.

**On-screen draft**

Why might this be true?

- Heisenberg's uncertainty principle ties a function to its time-frequency behavior.
- The free Schrodinger equation is morally Fourier.
- But many important models are not purely Fourier.

**Optional tiny formula**

`i \partial_t u + \Delta u = 0`

**Diagram suggestion**

- A bridge from `time-frequency information` to `wave evolution`.
- Or a left-right schematic: `Fourier world` -> `PDE world`.

**Speaker goal**

Explain the intuition: Fourier analysis already teaches us that limited information can be unexpectedly rigid.

---

### Frame 6. Going deeper

This is where the recent mathematics enters.

**On-screen draft**

Going deeper

- Recent breakthroughs in sphere packing led to discrete Fourier interpolation.
- Several PDE results already translate Fourier intuition into wave phenomena.
- The new question is whether discrete interpolation survives beyond the Fourier setting.

**Names to mention orally**

- Viazovska
- Radchenko and Viazovska

**Diagram suggestion**

- A simple bridge:
  `sphere packing / interpolation formulas` -> `unique continuation / PDE`

**Speaker goal**

Make the project feel timely and mathematically well-motivated, not speculative in a vacuum.

---

### Frame 7. Main conjecture

Keep the main statement non-technical on screen. Put the harder formulation in backup slides if needed.

**On-screen draft**

Main conjecture

Fixed sparse measurements in space and time can determine the whole wave.

Consequence:

- reconstruction from very limited data,
- first in linear models,
- then in nonlinear Schrodinger-type evolutions.

**Diagram suggestion**

- A space-time plane with a few highlighted sample points and a reconstructed wave surface.
- Or two rows of measurements, one at `t = 0` and one at `t = T`, feeding into a recovered evolution.

**Speaker goal**

Present the conjecture as both a conceptual claim and an algorithmic promise.

---

### Frame 8. Why this project stands out

This should mirror Braga's `Boldness, Originality, and Impact` frame.

**On-screen draft**

Why this project stands out

Boldness

- It asks for reconstruction well beyond the current Fourier formulas.

Originality

- It unifies harmonic analysis and dispersive PDE in a single framework.

Impact

- It changes how we think about partial observation of wave phenomena.
- It opens a route toward algorithmic reconstruction and simulation.

Positioning

- My work sits on both sides of this bridge: Fourier uniqueness and dispersive PDE.

**Speaker goal**

End the scientific case and the personal case on the same frame.

---

### Frame 9. Closing

Keep it short.

**On-screen draft**

Takeaway

Very little information may be enough to determine a wave.

Thank you.

**Visual suggestion**

- Reuse the title slide's wave image, now paired with a sparse sampling diagram.

**Optional last spoken line**

The project aims to turn that idea from Fourier intuition into a general principle for wave equations.

## Overlay Plan

To stay close to Braga's pacing:

- Frame 2: reveal institutions one at a time.
- Frame 3: reveal fields first, then one highlight at a time.
- Frame 4: show the big question first, then the three bullets.
- Frame 5: reveal the three motivation bullets sequentially.
- Frame 6: reveal the historical bridge in three steps.
- Frame 8: reveal `Boldness`, then `Originality`, then `Impact`, then `Positioning`.

## Practical Notes While Building The Slides

- Keep most frames under 5 lines of visible text at any moment.
- If you include equations, use them as visual anchors, not as proof material.
- Use images with clear shapes: ripples, sampling grids, spectrograms, wave packets.
- Prefer one strong diagram over a collage.
- If a frame starts looking dense, split it with overlays before adding more content.

## Picture / Diagram Wishlist

- `My path so far`: logos or a clean map with 3 to 5 nodes.
- `My work so far`: three-lane research diagram.
- `The big question`: real-world wave image plus sparse measurements.
- `Why might this be true?`: time-frequency plane feeding a wave evolution.
- `Going deeper`: bridge from discrete interpolation to PDE uniqueness.
- `Main conjecture`: sparse space-time samples reconstructing a continuous wave.
- `Closing`: same wave image, but now "explained" by a few discrete points.

## Two Good Title Variants

If you want a slightly more direct title:

1. `How much information is needed to reconstruct a wave?`
2. `Can a wave be recovered from sparse observations?`

The first is closer to the submitted project. The second is a bit punchier for slides.
