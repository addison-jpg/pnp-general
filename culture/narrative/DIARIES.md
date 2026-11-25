# Diaries: four diarists and one extension of Beauvoir

These are **readings** (analogy). Nothing here is a diagnosis: historical persons get readings, never diagnoses. Every source is **cited from memory**; none was re-read for this file. The one formal fact used is checked elsewhere: `core/ontology/beauvoir.py` (the frames in `narrative.ath` point at its check line). The story types are in `narrative.py`, on constructed stories only.

## The shared reading

A diary is a story told one step at a time, with no ending known in advance. In `narrative.py`'s terms it is a sequence of states. Arthur Frank's types (*The Wounded Storyteller*, 1995) ask how such a sequence ends: back where it began (restitution), somewhere other than where it began (quest), or without settling (chaos). The code's types are coarse proxies: its "quest" means only "not restored", so a story that goes from well to ill and stays ill counts, which Frank would not call a quest.

Lethargy, read here, is something else: a reached state that cannot go on. Beauvoir's condition, written []<>T, says that every world you can reach can itself reach something. `beauvoir.py` checks, on all 530 frames on 1 to 3 worlds, that []<>T holds exactly when the frame is successor-serial, and that a dead-end world is exactly what breaks it. Lethargy is that dead end: a reached world with no next step. This is the reading. The modal fact is checked-finite; that lethargy is such a world is analogy.

## Anais Nin (diaries published from 1966)

The diaries began in 1914 and were published, heavily edited, from 1966; unexpurgated volumes such as *Henry and June* (1986) and *Incest* (1992) came later (cited from memory). They are a deliberate self-construction: a curated story that the writer kept rewriting.

Stated plainly: Nin's writing is racist and exoticizing. Critics have documented how her diaries and her erotica present people of colour, and Black, Latin American and other non-white people in particular, as primitive, sensual or exotic: as scenery and as material for her own self-discovery, not as people with their own stories (cited from memory, to that criticism; no slurs are quoted here). Toni Morrison's *Playing in the Dark* (1992) names the pattern in white American writing: a white self defined against a constructed non-white presence. Edward Said's *Orientalism* (1978) names the exoticizing gaze. Both are cited from memory, and both fit Nin closely.

The link to this repository is the one-way arrow of `core/ontology/asymmetry.py`: one person narrates, others are narrated and cannot answer back. That is the 2-chain, a sees b and b does not see a. Frank's point that a story should belong to the one who lives it is broken here twice: Nin owns her story, and takes the stories of the people she exoticizes. This is analogy.

## Franz Kafka (diaries 1910-1923)

Kafka kept diaries from 1910 to 1923 (cited from memory). By day, from 1908 to 1922, he worked at the Workers' Accident Insurance Institute for the Kingdom of Bohemia in Prague. He wrote reports on accident prevention and handled claims (cited from memory). That work was bureaucratic, skilled and largely invisible: it does not appear in the literary record that made his name, and the writing was done at night around it.

This is Star and Strauss's invisible work (1999; cited from memory), and the information work Kim Unertl studies (`core/ontology/WORKFLOW.md`). Insurance for injured workers is a social good. It is carried by clerks whose work is seen only when it fails. The reading here: the day job is the keystone, the diary is the visible output. Analogy.

## Fyodor Dostoevsky (A Writer's Diary, 1873-1881; Notes from Underground, 1864)

*A Writer's Diary* was a public journal: first a column, then a monthly he wrote and published himself (cited from memory). It is a diary written to be read, the opposite of Nin's private-then-edited one.

It also has to be read critically. It contains antisemitic passages, most notoriously on "the Jewish question" in 1877, and a Russian nationalist and imperial programme, including the wish for Constantinople (cited from memory). These are stated here as part of the record, not set aside.

*Notes from Underground* (1864) is aimed at the Crystal Palace, the image of a finished rational society taken from Chernyshevsky's *What Is to Be Done?* (1863; cited from memory). The underground man refuses a world where two times two makes four is the last word, and says that consciousness itself leads to inertia (described, not quoted). The critique of the rationalist utopia is sharp. It also stays in thought: he does not go anywhere.

Two dead ends, read together. The Crystal Palace is a world that, once reached, has nowhere further to go: a utopia as a dead end, the thing []<>T forbids. The underground man's refusal is the demand that the world go on. But his own inertia is a dead end too. Analogy.

## Virginia Woolf (diary 1915-1941)

Woolf kept a diary from 1915 to 1941, published in five volumes edited by Anne Olivier Bell (cited from memory). She died on 28 March 1941. That is the fact; nothing more is said here about it.

The diary also needs a critical reading. It has antisemitic remarks, including about her husband Leonard's family, and class contempt, especially about the servants who ran the house (cited from memory). Alison Light's *Mrs Woolf and the Servants* (2007; cited from memory) reads that household as invisible work: the cooking and cleaning that made the writing possible, by women such as Nellie Boxall who appear in the diary mostly as irritations.

The reading: the diary is a sequence that keeps going for 26 years. Its going on is held up by work the diary does not credit. Analogy.

## Simone de Beauvoir (her own diaries)

Beauvoir's student diaries (*Cahiers de jeunesse*, 1926-1930, published 2008) and her *Wartime Diary* (1939-1941, published 1990) are cited from memory. In *The Ethics of Ambiguity* (1947) she argues that to will oneself free is also to will others free (described, not quoted).

Critical note: readers in Black feminist thought have criticised *The Second Sex* (1949) for its analogy between women and Black Americans, which treats the two as separate groups and leaves Black women out (cited from memory). Her *America Day by Day* (1948) writes about race in the United States from a visitor's distance (cited from memory).

**The extension.** `beauvoir.py` gives two conditions. <>T (serial): every world can go on. []<>T (successor-serial): every world I can reach can go on. The second is weaker, and the gap is exact: frames where some world reaches nothing, but no world reaches it. Read as ethics: I may stand at a dead end myself, but I may not lead anyone into one. Read as a diary: a story may stall, but it must not stall someone else's. Nin's exoticized subjects, Woolf's servants and Kafka's claimants are the reached worlds whose going on the writer's story did not secure. The formal fact is checked-finite; this reading is analogy.

## Fisher and hauntology: anachronistic, and still useful

Mark Fisher, *Capitalist Realism* (2009) and *Ghosts of My Life* (2014), cited from memory: the slow cancellation of the future, a culture that can no longer imagine anything new, and depression read as a social state rather than only a private one. Hauntology is Derrida's word (*Specters of Marx*, 1993; cited from memory), used by Fisher for late twentieth-century culture.

Applying this to writers of 1864 to 1941 is **anachronistic**. Fisher wrote about neoliberal Britain after about 1980. These writers lived before it, and their futures were open in ways his were not.

What it still illuminates: Fisher's question is when a future stops being reachable, and whether that is a private failing or a social fact. Dostoevsky's Crystal Palace is an early form of a future declared finished. Kafka's office is a system that goes on without anyone being able to change it. Read this way, lethargy is not a personal flaw. It is a reached world that the surrounding structure has left without a next step. That is the sense of the dead end used above. Analogy.

## Labels

| claim | label |
|---|---|
| []<>T holds exactly when the frame is successor-serial; a dead end breaks it (530 frames, 1..3 worlds) | checked-finite (`core/ontology/beauvoir.py`) |
| story type counts and the non-compositionality of joined lives | checked-finite (`narrative.py`, constructed stories) |
| dates, publications and the documented criticism above | cited from memory |
| lethargy as a dead-end world; every link to the diarists | analogy |
| hauntology applied before 1980 | analogy, marked anachronistic |
