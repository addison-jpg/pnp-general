# Workflow, after Kim M. Unertl: the high level of how this repository works

Kim M. Unertl (Vanderbilt University Medical Center, Department of Biomedical Informatics) studies clinical workflow, coordination and collaboration, information flow and "invisible" work, mostly with direct observation, interviews and qualitative analysis. Her frameworks fit this repository's own way of working closely, so this file reads the repository through them. **Read status:** every paper below was read as its abstract and metadata only (OpenAlex, 2026-11-25); full texts were not reachable from this container. Anything beyond the abstract is marked cited from memory. **Labels:** each mapping is a reading (analogy) unless it names a computed number.

## Her work, cited

1. Unertl KM, Novak LL, Johnson KB, Lorenzi NM. Traversing the many paths of workflow research: developing a conceptual framework of workflow terminology through a systematic literature review. *JAMIA* 2010;17(3):265-273. doi:10.1136/jamia.2010.004333. From 6,221 abstracts, 127 articles; ethnographic observation and interviews were the most used methods; triangulation was the most discussed check on quality; the definition of "workflow" varied widely; a conceptual framework of workflow terminology is proposed.
2. Unertl KM, Weinger MB, Johnson KB, Lorenzi NM. Describing and modeling workflow and information flow in chronic disease care. *JAMIA* 2009;16(6):826-836. doi:10.1197/jamia.m3000. Over 150 hours of observation in three clinics, 157 patient-provider interactions, open coding; workflow and information flow modelled **separately**, with Hierarchical Task Analysis and Soft Systems Methodology; nine interviews to confirm the models.
3. Unertl KM, Johnson KB, Lorenzi NM. Health information exchange technology on the front lines of healthcare: workflow factors and patterns of use. *JAMIA* 2012;19(3):392-400. doi:10.1136/amiajnl-2011-000432. Six emergency departments and eight clinics, over 180 hours; large site-to-site differences, and two **role-based** workflow models (nurse based, physician based); the workflow elements framework applied.
4. Unertl KM, Johnson KB, Gadd CS, Lorenzi NM. Bridging organizational divides in health care: an ecological view of health information exchange. *JMIR Med Inform* 2013;1(1):e3. doi:10.2196/medinform.2510. The Regional Health Information Ecology, analysed by five components: **system, locality, diversity, keystone species, coevolution** (an information-ecology frame; its origin in Nardi and O'Day, *Information Ecologies*, 1999, is cited from memory).
5. Mickelson RS, Unertl KM, Holden RJ. Medication management: the macrocognitive workflow of older adults with heart failure. *JMIR Hum Factors* 2016;3(2):e27. doi:10.2196/humanfactors.6338. Macrocognition: how people think, alone and together, in complex, adaptive, messy settings supported by artifacts.
6. Novak LL, Anders SH, Unertl KM, France DJ, Weinger MB. Improving the effectiveness of health information technology: the case for situational analytics. *Appl Clin Inform* 2019;10(5):771-776. doi:10.1055/s-0039-1697594. Analytic methods that characterise activity in situations, from trace data (EHR activity logs), user reports, field data and location data.
7. Unertl KM, Novak LL, Van Houten C, et al. Organizational diagnostics: a systematic approach to identifying technology and workflow issues in clinical settings. *JAMIA Open* 2020;3(2):199-208. doi:10.1093/jamiaopen/ooaa013. Systematic Iterative Organizational Diagnostics (SIOD), five stages: background scan, engagement building, data acquisition, data analysis, reporting and debriefing.
8. Ancker JS, Benda NC, Reddy MC, Unertl KM, Veinot TC. Guidance for publishing qualitative research in informatics. *JAMIA* 2021;28(12):2743-2748. doi:10.1093/jamia/ocab195. Report theory, question, sampling, data collection, analysis, results and discussion, so readers can judge rigour.
9. Unertl KM, Abraham J, Bakken S. Building on Diana Forsythe's legacy: the value of human experience and context in biomedical and health informatics. *JAMIA* 2021;28(5):1093-1097. doi:10.1093/jamia/ocaa337. Forsythe brought anthropology and the social study of science into AI and informatics.
10. Ozkaynak M, Haque SN, Unertl KM, Kuziemsky CE. Pragmatic approaches for studying workflow in health informatics. *JAMIA Open* 2026. doi:10.1093/jamiaopen/ooag044. Five principles, **relevance, actionability, comprehensibility, ethical reasoning, iterative assessment**, and a six-step guideline; pragmatic studies trade some rigour for fewer resources, and that trade-off has to be managed.

(Volume and page numbers for items 4 to 9 are from memory where the abstract record did not give them; the DOIs are from OpenAlex and are exact.)

## The repository, read through her frameworks

| her idea | in this repository | label |
|---|---|---|
| workflow and information flow are different and are modelled separately (2) | boards and task files carry the workflow; the centre store (`center/shards`) carries the information flow | reading |
| Hierarchical Task Analysis (2) | `boards/TREE.md`: findings carried up the directory tree | reading |
| role-based workflow models (3) | seats by role (build, review, repair) and by size (Haiku, Sonnet, Opus); `workshop/ath_prompts/us/` checks the assignment's stability on recorded data | reading; the stability check is its own result |
| triangulation as the quality check (1) | the second seat: every non-Lean finding needs an independent seat before it counts as verified | reading |
| information ecology: system, locality, diversity, keystone species, coevolution (4) | system = `big.ath`; locality = the pillar folders; diversity = 24 universes; coevolution = lateral links; keystone species = a universe whose removal splits the map | reading, with one number below |
| macrocognition supported by artifacts (5) | boards, frames and records are the artifacts the seats think with | reading |
| situational analytics from trace data (6) | git history and the findings log are the trace data; the planned event log (born, confirmed, refuted) is the analytic | reading; plan |
| SIOD's five stages (7) | a workflow here: scan the repo, brief the seat, build, review, repair and report | reading |
| reporting guidance for qualitative work (8) | the label rule: every claim says what checked it and how far | reading |
| pragmatic workflow principles (10) | Addison's "cheap methods first": trade rigour for cost on purpose, and say so in the label | reading |

**Keystone species, computed** (from `center/shards`, 2026-11-25): on the map of 24 universes and 8 lateral links, the universes whose removal splits a connected piece are **asteroid, brain, circuits, philosophy and transit**. Every other universe is a leaf or isolated. This is exact for the current map; the map changes as findings are added (`philosophy/cone.py`).

## Why her work is the right high level

Her finding that "workflow" means different things in different fields (1) is the same problem this repository has with labels across pillars, and her answer is the same one used here: say exactly which sense is meant, and check it by more than one route. Her pragmatic principles (10) are a published, reviewed version of the cheap-first rule. Addison's own background in informatics (AMIA) is the same field.

## Open

1. Read the full texts of (1) and (4) when a source is reachable, and record the conceptual framework's exact components.
2. Apply the workflow elements framework of (3) to the seat logs.
3. Use SIOD (7) on this repository itself, once, as a written diagnostic.
