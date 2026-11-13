# Typography for long-form reading on screen: a short review for the Studio

*Status: design note, November 2026. Scope: the left panel of StoryLangLib Studio, where a story is read in long stretches, in dark or light mode, with optional annotations. What is decided here is in `studio/web/src/reading.css`.*

The evidence base for on-screen reading typography is thinner and noisier than designers' rules of thumb suggest. Most effects are small; several are significant only for particular readers (dyslexic readers, low vision, older readers); and preference and performance often disagree. The working rule is: follow the long-standing book conventions where the screen evidence does not contradict them, and give readers control where it does.

## 1. Line length (measure)

**Print tradition.** Bringhurst (*The Elements of Typographic Style*, 1992/2004, §2.1.2) puts the comfortable measure for a single column of serif text at 45–75 characters, 66 ideal. Tinker's legibility studies (*Legibility of Print*, 1963) found reading speed fell off for very short (under about 3 in at 10 pt) and very long lines.

**On screen.** Dyson & Haselgrove ("The influence of reading speed and line length on the effectiveness of reading from screen", *IJHCS* 2001) found that long lines (~100 cpl) were read faster but comprehension was best at medium lengths (~55 cpl). Dyson's review ("How physical text layout affects reading from screen", *Behaviour & IT* 2004) concludes that faster scanning at long measures comes at the cost of comprehension, and that readers *prefer* moderate lines. Shaikh's "The effects of line length on reading online news" (*Usability News* 2005) reproduces the speed/preference split. Beymer, Russell & Orton ("An eye tracking study of how font size and type influence online reading", *BCS HCI* 2008) see more regressions with long lines.

**Decision.** Measure `max-width: 66ch` (about 62–70 characters with the chosen face), never more than 75; on phones the measure is whatever the screen gives, with 1.25 rem side gutters.

## 2. Size

Rello, Pielot & Marcos ("Make it big! The effect of font size and line spacing on online readability", *CHI* 2016) eye-tracked 104 readers on Wikipedia text: comprehension and reading time improved with size up to 18 pt and plateaued at 22 pt; line spacing (0.8–1.8) had no significant effect on readability within the tested range, though it affected preference. Bernard, Liao & Mills ("The effects of font type and size on the legibility and reading time of online text by older adults", *CHI EA* 2001) found 14 pt better than 12 pt for older readers. Legge & Bigelow ("Does print size matter for reading?", *Journal of Vision* 2011) show reading speed is flat across a wide "fluent range" above critical print size, so bigger is safe and too small is costly.

**Decision.** Body text at 20 px (1.25 rem) on desktop, 18 px on narrow screens, user-adjustable (A−/A+); never below 16 px.

## 3. Leading

Book convention is 120–145% of the size for text faces (Bringhurst §2.2). Screens are read from further away and at lower resolution, and web guidance (WCAG 2.1 SC 1.4.12, Text Spacing) requires that content survive line height 1.5. Chaparro, Shaikh & Chaparro ("Examining the legibility of two new ClearType fonts", *Usability News* 2006) and the Rello et al. study above find leading matters less than size, but very tight leading increases mis-sweeps when returning to the next line, worse with long lines. Leading should grow with the measure.

**Decision.** `line-height: 1.6` for body. The overview mode needs room under the baseline for underlines and a little room above for marks; 1.6 provides it without changing the layout between chill and overview, which matters (Section 8).

## 4. Typeface

Serif versus sans on screen is close to a null result once resolution is decent: Bernard et al. ("A comparison of popular online fonts", *Usability News* 2001; "Comparing the effects of text size and format on the readability of computer-displayed Times New Roman and Arial text", *IJHCS* 2003) found no reliable reading-time differences, only preferences; Arditi & Cho ("Serifs and font legibility", *Vision Research* 2005) found serifs neither help nor hurt. On high-DPI screens the long-form convention (serif for immersive reading) is a matter of genre and comfort, and readers of fiction expect it. What does matter: generous x-height, open counters, and moderate contrast between thick and thin strokes; hairline-thin strokes degrade in dark mode (halation, below). Rello & Baeza-Yates ("Good fonts for dyslexia", *ASSETS* 2013) found sans, roman, monospaced faces read better by dyslexic readers, and italics worse.

**Decision.** Literata (designed for long-form e-reading, Google Play Books; large x-height, sturdy serifs, optical sizes) as body, with Source Serif 4 and Georgia as fallbacks; italics only where the text has them. A sans (Inter) for UI chrome and the logic panel, so prose and machinery never look alike. A user switch to a sans body (Atkinson Hyperlegible) for readers who prefer it.

## 5. Contrast and colour; dark mode

Polarity: Piepenbrock, Mayr, Mund & Buchner ("Positive display polarity is advantageous for both younger and older adults", *Ergonomics* 2013) and Buchner & Baumgartner (*Ergonomics* 2007) show dark-on-light text is read better than light-on-dark, attributed to smaller pupils and sharper focus under brighter screens. Light-on-dark suffers *halation* (bright strokes bleed), worse for astigmatic readers (roughly a third to a half of adults). But dark mode is preferred at night and in dim rooms, and the effect sizes are small. So: offer both, default to the system preference, remember the choice.

Contrast: WCAG 2.x requires 4.5:1 for body text (AA), 7:1 for AAA. Maximal contrast (pure black on pure white, or pure white on pure black) is not best for long reading: designers since Tschichold have recommended off-white paper; on screens pure white backgrounds raise glare, and pure white text on black maximises halation. The recommended range is roughly 10:1–15:1 for long-form.

**Decision.**
- Light: text `#2b2622` on paper `#fbf8f2` (≈ 14:1); muted text `#6b6259`.
- Dark: text `#d9d2c5` on `#1b1a18` (≈ 12:1), warm and slightly dim to reduce halation; no pure white anywhere in body text. Annotation colours are chosen per theme so each keeps ≥ 3:1 against the background (WCAG 1.4.11 for non-text marks) without being saturated.

## 6. Justification, hyphenation, ragged right

Justified text without hyphenation on narrow measures produces rivers and uneven word spacing; Trollip & Sales ("Readability of computer-generated fill-justified text", *Human Factors* 1986) found fill-justified text read slower than ragged-right on screen, and Gregory & Poulton (*Ergonomics* 1970) found justified text harder for weaker readers on narrow measures. Browsers' justification is greedy (line by line, not Knuth–Plass), so it spaces worse than a book. Hyphenation (CSS `hyphens: auto`) mitigates the spacing but splits names, and the Studio anchors annotations to tokens; a split token makes an underline break across lines.

**Decision.** Ragged right, `hyphens: manual` (no automatic hyphenation), `text-wrap: pretty` to avoid one-word last lines where supported, `hanging-punctuation: first` for opening quotes (Safari only, harmless elsewhere).

## 7. Paragraphs and rhythm

Fiction convention is first-line indent with no space between paragraphs (Bringhurst §2.3.1); the web convention is a blank line. Indents keep the column visually continuous, which suits immersion; spaces make each paragraph a block, which suits a two-panel layout where each paragraph is aligned with its logic on the right. The Studio's thread is per paragraph, so paragraph boundaries are functional, not just visual.

**Decision.** Chill mode: book style, 1.5 em first-line indent, no indent after a scene break, `0.4em` between paragraphs (a hint of the boundary without breaking the column). Overview mode: the same, plus a faint paragraph number in the left margin, which is the anchor the right panel scrolls to. Scene breaks as a centred asterism with extra space.

## 8. Annotation without clutter

The overview layer must not reflow the text. Two findings shape this. First, layout shifts disrupt reading position: anything that changes line breaks as annotations toggle forces the reader to re-find their place (the same reason Google's Core Web Vitals penalise layout shift). Second, glossing research on L2 reading (e.g. Abraham, "Computer-mediated glosses in second language reading comprehension", *CALL* 2008, a meta-analysis) finds marginal and pop-up glosses help comprehension without the cost of inline interruption; Chen et al.'s work on in-text highlighting finds that dense highlighting stops helping once more than a small fraction of text is marked.

**Decision.**
- Annotations use only properties that do not change layout: `text-decoration` (underline colour, style and offset), `background` with low alpha, `box-shadow`, margin marks positioned absolutely, and hover/focus cards. No inserted text, no font-weight changes, no padding on inline spans.
- Entity mentions: an underline in the character's colour (2 px, offset 0.2 em); pronouns dotted, names solid, so forward/backward references read differently; hovering a mention highlights every mention of the same entity.
- Parts of speech: off by default; when on, a very faint tint by coarse class (verbs, nouns) at 6–8% alpha.
- Quotes: a thin left rule in the speaker's colour in the margin beside lines containing the speaker's quote, plus the speaker's initial.
- Events: the verb token of each clause the lexicon reads gets a small dot under it; hover shows the event.
- Time words: dashed underline in a neutral colour.
- Warnings: a margin mark (a small coloured glyph) on the line, never a squiggle across the text; hover shows `why`.
- At most two decoration channels on any one token; when more apply, the less important ones move to the hover card.

## 9. Interaction

Keep chrome out of the reading area: toggles in a small header that fades when scrolling; keyboard shortcuts (`d` theme, `o` overview, `j/k` paragraph). Remember theme, mode and size in `localStorage`. Respect `prefers-reduced-motion` (no smooth-scroll sync animation) and `prefers-color-scheme` (initial theme).

## References (selected)

- Arditi, A. & Cho, J. (2005). Serifs and font legibility. *Vision Research* 45(23).
- Bernard, M., Liao, C. & Mills, M. (2001). The effects of font type and size on the legibility and reading time of online text by older adults. *CHI EA*.
- Beymer, D., Russell, D. & Orton, P. (2008). An eye tracking study of how font size and type influence online reading. *BCS HCI*.
- Bringhurst, R. (2004). *The Elements of Typographic Style*, 3rd ed. Hartley & Marks.
- Buchner, A. & Baumgartner, N. (2007). Text–background polarity affects performance irrespective of ambient illumination and colour contrast. *Ergonomics* 50(7).
- Dyson, M. C. (2004). How physical text layout affects reading from screen. *Behaviour & Information Technology* 23(6).
- Dyson, M. C. & Haselgrove, M. (2001). The influence of reading speed and line length on the effectiveness of reading from screen. *IJHCS* 54(4).
- Legge, G. E. & Bigelow, C. A. (2011). Does print size matter for reading? A review of findings from vision science and typography. *Journal of Vision* 11(5).
- Piepenbrock, C., Mayr, S., Mund, I. & Buchner, A. (2013). Positive display polarity is advantageous for both younger and older adults. *Ergonomics* 56(7).
- Rello, L. & Baeza-Yates, R. (2013). Good fonts for dyslexia. *ASSETS*.
- Rello, L., Pielot, M. & Marcos, M.-C. (2016). Make it big! The effect of font size and line spacing on online readability. *CHI*.
- Tinker, M. A. (1963). *Legibility of Print*. Iowa State University Press.
- Trollip, S. R. & Sales, G. (1986). Readability of computer-generated fill-justified text. *Human Factors* 28(2).
- W3C (2018). Web Content Accessibility Guidelines 2.1 (SC 1.4.3, 1.4.11, 1.4.12).
