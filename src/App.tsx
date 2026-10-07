import { useEffect, useState, type ReactNode } from "react";
import { Check, Copy, Play } from "lucide-react";

type Language = "rust" | "ruby" | "ocaml" | "python" | "lisp";
type Layer = "unified" | "code" | "lifetimes" | "types" | "invariants" | "performance";
type ProgramViews = Record<Layer, string[]>;

const languages: { id: Language; label: string; extension: string }[] = [
  { id: "rust", label: "Rust-like", extension: "rs" },
  { id: "ruby", label: "Ruby-like", extension: "rb" },
  { id: "ocaml", label: "OCaml-like", extension: "ml" },
  { id: "python", label: "Python-like", extension: "py" },
  { id: "lisp", label: "Lisp-like", extension: "lisp" },
];

const layerDefinitions: { id: Layer; label: string; stem: string }[] = [
  { id: "unified", label: "Unified", stem: "foo.unified" },
  { id: "code", label: "Logic", stem: "foo" },
  { id: "lifetimes", label: "Lifetimes", stem: "foo.lifetimes" },
  { id: "types", label: "Types", stem: "foo.types" },
  { id: "invariants", label: "Invariants", stem: "foo.invariants" },
  { id: "performance", label: "Performance", stem: "foo.performance" },
];

const lines = (source: string) => source.trim().split("\n");

const programs: Record<Language, ProgramViews> = {
  rust: {
    unified: lines(`
#[perf(inline(rank) = auto, heap_allocations = 0, evaluation = lazy)]
#[perf(materialize = false, padding(candidates) = none, copies_per_item = 0)]
type Predicate<'query, 'docs> = FnMut(&&'docs Document) -> bool + 'query;
fn rank<'query, 'docs>(
    immutable query: &'query str,
    docs: &'docs [Document],
) -> impl Iterator<Item = &'docs Document> + 'query + 'docs
ensures {
    arity(rank) = 2;
    result ⊆ docs;
    matches_all(result, query);
    preserves_order(result, docs);
    value_after(query) = value_before(query);
}
{
    let candidates: Iter<'docs, Document> = docs.iter();
    invariant {
        count(candidates) = count(docs);
        order(candidates) = order(docs);
        elements(candidates) ⊆ docs;
    };
    let matching: Filter<
        Iter<'docs, Document>,
        Predicate<'query, 'docs>
    > = candidates.filter(move |doc: &&'docs Document| -> bool {
        doc.title().contains(query)
    });
    matching
}`),
    code: lines(`
fn rank(query, docs) {
    let candidates = docs.iter();
    candidates.filter(|doc| doc.title().contains(query))
}`),
    lifetimes: lines(`
fn rank<'query, 'docs>(
    query: &'query str,
    docs: &'docs [Document],
) -> impl Iterator<Item = &'docs Document> + 'query + 'docs {
    let candidates: Iter<'docs, Document> = docs.iter();
    candidates.filter(move |doc: &&'docs Document| doc.title().contains(query))
}`),
    types: lines(`
type DocumentRef = &Document
fn rank(query: &str, docs: &[Document]) -> Iterator<DocumentRef>
let candidates: Iter<DocumentRef> = iter(docs)
let predicate: DocumentRef → bool = matches_title(query)
let matching: Filter<Iter<DocumentRef>, Fn<DocumentRef, bool>> = filter(candidates, predicate)
return matching`),
    invariants: lines(`
invariant rank {
    arity(rank) == 2
    result(rank, query, docs) ⊆ docs
    ∀ doc ∈ result: matches(doc.title, query)
    order(result) = order(docs filtered by query)
}
invariant query {
    immutable(query)
    value_after(rank, query) = value_before(rank, query)
}
invariant candidates {
    count(candidates) = count(docs) ∧ order(candidates) = order(docs)
    elements(candidates) ⊆ docs
}`),
    performance: lines(`
plan rank {
    inline(rank) = auto
    return = lazy_iterator
    heap_allocations = 0
}
plan candidates {
    representation = slice_iterator
    copies_per_item = 0
    padding(candidates) = none
}
plan matching {
    evaluation = on_consume
    materialize = false
}`),
  },
  ruby: {
    unified: lines(`
perf :rank, inline: :auto, heap_allocations: 0, evaluation: :lazy
perf :rank, materialize: false, copies_per_item: 0
perf :candidates, representation: :slice_enumerator, padding: :none
type Predicate = Proc[Borrowed[Document, :docs], Bool] captures: :query
def rank(
  immutable query: Borrowed[String, :query],
  docs: Borrowed[List[Document], :docs]
) -> Iterator[Borrowed[Document, :docs], captures: :query]
ensures :rank do
  arity(:rank) == 2
  result.subset_of?(docs)
  result.all? { |doc| doc.title.include?(query) }
  result.order == docs.select { |doc| doc.title.include?(query) }.order
  query.after(:rank) == query.before(:rank)
end
candidates = docs.each
invariant :candidates do
  candidates.count == docs.count
  candidates.order == docs.order
  candidates.all? { |doc| docs.include?(doc) }
end
matching: Filter[Enumerator[Borrowed[Document, :docs]], Predicate] = candidates.select do |doc|
  doc.title.include?(query)
end
matching
end`),
    code: lines(`
def rank(query, docs)
  candidates = docs.each
  candidates.select { |doc| doc.title.include?(query) }
end`),
    lifetimes: lines(`
def rank(query: Borrowed[String, :query], docs: Borrowed[List[Document], :docs])
  -> Iterator[Borrowed[Document, :docs], captures: :query]
  candidates = docs.each
  candidates.select { |doc: Borrowed[Document, :docs]| doc.title.include?(query) }
end`),
    types: lines(`
DocumentRef = Borrowed[Document]
def rank(query: StringRef, docs: Slice[Document]) -> Iterator[DocumentRef]
candidates: Enumerator[DocumentRef] = docs.each
predicate: Proc[DocumentRef, Bool] = matches_title(query)
matching: Select[Enumerator[DocumentRef], predicate] = candidates.select(predicate)
return matching`),
    invariants: lines(`
invariant :rank do
  arity(:rank) == 2
  result(:rank, query, docs).subset_of?(docs)
  result.all? { |doc| doc.title.include?(query) }
  result.order == docs.select { |doc| doc.title.include?(query) }.order
end
invariant :query do
  immutable(:query)
  query.after(:rank) == query.before(:rank)
end
invariant :candidates do
  candidates.count == docs.count
  candidates.order == docs.order
  candidates.all? { |doc| docs.include?(doc) }
end`),
    performance: lines(`
performance :rank do
  inline :auto
  heap_allocations 0
  evaluation :lazy
  materialize false
end
performance :candidates do
  representation :slice_enumerator
  copies_per_item 0
  padding :none
end
performance :matching do
  evaluation :on_consume
  materialize false
end`),
  },
  ocaml: {
    unified: lines(`
[@@@perf inline(rank) = auto]
[@@@perf heap_allocations(rank) = 0; evaluation(rank) = lazy]
[@@@perf materialize(rank) = false; padding(candidates) = none; copies_per_item = 0]
type ('query, 'docs) predicate = Document ref<'docs> -> bool captures 'query
val rank :
  immutable query: string ref<'query> ->
  docs: Document list ref<'docs> ->
  Document seq<'docs> captures 'query
ensures rank:
  arity rank = 2
  result rank query docs ⊆ docs
  matches_all result query
  preserves_order result docs
  value_after query = value_before query
let rank query docs =
  let candidates : Document seq<'docs> = Seq.of_list docs in
  invariant candidates:
    length candidates = length docs
    order candidates = order docs
    elements candidates ⊆ docs
  let matching : Filter[Document seq<'docs>, predicate<'query, 'docs>] =
    Seq.filter (fun (doc : Document ref<'docs>) -> contains doc.title query) candidates in
  matching`),
    code: lines(`
let rank query docs =
  let candidates = List.to_seq docs in
  Seq.filter (fun doc -> contains doc.title query) candidates`),
    lifetimes: lines(`
type ('query, 'docs) predicate = Document ref<'docs> -> bool captures 'query
val rank :
  immutable query: string ref<'query> ->
  docs: Document list ref<'docs> ->
  Document seq<'docs> captures 'query
let candidates : Document seq<'docs> = Seq.of_list docs
Seq.filter (fun (doc : Document ref<'docs>) -> contains doc.title query) candidates`),
    types: lines(`
type document_ref = Document ref
val rank : string ref -> Document list ref -> document_ref Seq.t
let candidates : document_ref Seq.t = Seq.of_list docs
let predicate : document_ref -> bool = matches_title query
let matching : document_ref Seq.t = Seq.filter predicate candidates
matching`),
    invariants: lines(`
invariant rank =
  arity rank = 2
  result rank query docs ⊆ docs
  ∀ doc ∈ result: contains doc.title query
  ordered result = filtered_order docs query
invariant query =
  immutable query
  value_after rank query = value_before rank query
invariant candidates =
  length candidates = length docs
  order candidates = order docs
  elements candidates ⊆ docs`),
    performance: lines(`
[@@perf inline(rank) = auto]
[@@perf heap_allocations(rank) = 0]
[@@perf evaluation(rank) = lazy]
[@@perf materialize(rank) = false]
[@@perf padding(candidates) = none]
[@@perf copies_per_item = 0]
[@@perf representation(candidates) = slice_iterator]
[@@perf evaluation(matching) = on_consume]`),
  },
  python: {
    unified: lines(`
@perf(inline=auto, heap_allocations=0, evaluation="lazy")
@perf(materialize=False, copies_per_item=0, padding={"candidates": None})
Predicate: TypeAlias = Callable[[Borrowed[Document, 'docs]], bool], captures='query
def rank(
    immutable query: Borrowed[str, 'query],
    docs: Borrowed[list[Document], 'docs],
) -> Iterator[Borrowed[Document, 'docs], captures=('query, 'docs)]:
    ensures(
        arity(rank) == 2,
        result <= docs,
        matches_all(result, query),
        preserves_order(result, docs),
        value_after(query) == value_before(query),
    )
    candidates: Iterator[Borrowed[Document, 'docs]] = iter(docs)
    invariant(
        len(candidates) == len(docs),
        order(candidates) == order(docs),
        elements(candidates) <= docs,
    )
    matching: Filter[Iterator[Borrowed[Document, 'docs]], Predicate] = filter(
        lambda doc: doc.title.contains(query), candidates
    )
    return matching`),
    code: lines(`
def rank(query, docs):
    candidates = iter(docs)
    return (doc for doc in candidates if query in doc.title)`),
    lifetimes: lines(`
Predicate = Callable[[Borrowed[Document, 'docs]], bool], captures='query
def rank(
    immutable query: Borrowed[str, 'query],
    docs: Borrowed[list[Document], 'docs],
) -> Iterator[Borrowed[Document, 'docs], captures='query]:
    candidates: Iterator[Borrowed[Document, 'docs]] = iter(docs)
    return filter(lambda doc: query in doc.title, candidates)`),
    types: lines(`
DocumentRef = Ref[Document]
def rank(query: str, docs: Sequence[Document]) -> Iterator[DocumentRef]:
candidates: Iterator[DocumentRef] = iter(docs)
predicate: Callable[[DocumentRef], bool] = matches_title(query)
matching: Filter[Iterator[DocumentRef], Predicate] = filter(predicate, candidates)
return matching`),
    invariants: lines(`
invariant rank:
    assert arity(rank) == 2
    assert result(rank, query, docs) <= docs
    assert all(matches(doc.title, query) for doc in result)
    assert preserves_order(result, docs)
invariant query:
    assert immutable(query)
    assert value_after(rank, query) == value_before(rank, query)
invariant candidates:
    assert len(candidates) == len(docs)
    assert order(candidates) == order(docs)
    assert elements(candidates) <= docs`),
    performance: lines(`
@perf(inline="auto")
@perf(heap_allocations=0)
@perf(evaluation="lazy")
@perf(materialize=False)
@perf(padding={"candidates": None})
@perf(copies_per_item=0)
@perf(representation="slice_iterator")
@perf(evaluation_of="matching", timing="on_consume")`),
  },
  lisp: {
    unified: lines(`
(perf rank :inline :auto :heap-allocations 0 :evaluation :lazy)
(perf rank :materialize false :copies-per-item 0 :padding (candidates :none))
(type Predicate ('query 'docs)
  (fn ((borrowed Document 'docs)) Bool)
  (captures 'query))
(define (rank
  (immutable query (borrowed String 'query))
  (docs (borrowed (List Document) 'docs)))
  (returns (Iterator (borrowed Document 'docs) :captures ('query 'docs)))
  (ensures
    (= (arity rank) 2)
    (subset? result docs)
    (matches-all? result query)
    (preserves-order? result docs)
    (= (value-after query) (value-before query)))
  (let ((candidates (iter docs :type (Iter 'docs Document))))
    (invariant candidates
      (= (count candidates) (count docs))
      (= (order candidates) (order docs))
      (subset? (elements candidates) docs))
    (let ((matching
      (filter candidates
        (lambda ((doc (borrowed Document 'docs)))
          (contains? (title doc) query)))))
      matching)))`),
    code: lines(`
(defun rank (query docs)
  (let ((candidates (iter docs)))
    (filter (lambda (doc) (contains? (title doc) query)) candidates)))`),
    lifetimes: lines(`
(type Predicate ('query 'docs)
  (fn ((borrowed Document 'docs)) Bool)
  (captures 'query))
(define (rank
  (immutable query (borrowed String 'query))
  (docs (borrowed (List Document) 'docs)))
  (returns (Iterator (borrowed Document 'docs) :captures ('query 'docs)))
  (let ((candidates (iter docs :type (Iter 'docs Document))))
    (filter
      (lambda ((doc (borrowed Document 'docs)))
        (contains? (title doc) query))
      candidates)))`),
    types: lines(`
(type DocumentRef (Ref Document))
(fn-type rank (-> ((query StringRef) (docs (Slice Document))) (Iterator DocumentRef)))
(let ((candidates (Iter DocumentRef) (iter docs)))
  (let ((predicate (Fn DocumentRef Bool) (matches-title query)))
    (let ((matching (Filter (Iter DocumentRef) Predicate) (filter candidates predicate)))
      matching)))`),
    invariants: lines(`
(invariant rank
  (= (arity rank) 2)
  (subset? (result rank query docs) docs)
  (forall (doc (result rank query docs))
    (matches? (title doc) query))
  (preserves-order? (result rank query docs) docs))
(invariant query
  (immutable query)
  (= (value-after query rank) (value-before query rank)))
(invariant candidates
  (= (count candidates) (count docs))
  (= (order candidates) (order docs))
  (subset? (elements candidates) docs))`),
    performance: lines(`
(perf rank
  (inline auto)
  (heap-allocations 0)
  (evaluation lazy)
  (materialize false))
(perf candidates
  (representation slice-iterator)
  (copies-per-item 0)
  (padding none))
(perf matching
  (evaluation on-consume)
  (materialize false))`),
  },
};

const keywords: Record<Language, Set<string>> = {
  rust: new Set(["fn", "let", "type", "impl", "move", "invariant", "ensures", "immutable", "return", "plan"]),
  ruby: new Set(["def", "end", "do", "type", "invariant", "performance", "perf", "immutable"]),
  ocaml: new Set(["let", "in", "type", "val", "fun", "immutable", "invariant", "ensures"]),
  python: new Set(["def", "return", "in", "for", "if", "type", "invariant", "assert", "immutable", "ensures"]),
  lisp: new Set(["define", "defun", "let", "type", "invariant", "perf", "immutable", "lambda", "returns", "ensures"]),
};

function classForToken(token: string, language: Language) {
  if (token.startsWith("#") || token.startsWith("@")) return "syntax-attribute";
  if (/^'[A-Za-z_][\w]*$/.test(token)) return "syntax-lifetime";
  if (/^\d+$/.test(token)) return "syntax-number";
  if (keywords[language].has(token)) return "syntax-keyword";
  if (/^[A-Z][A-Za-z\d_]*$/.test(token)) return "syntax-type";
  if (["rank", "title", "iter", "filter", "select", "matches_title", "contains", "Seq", "List"].includes(token)) return "syntax-method";
  if (["query", "docs", "doc"].includes(token)) return "syntax-parameter";
  if (["candidates", "matching", "result", "predicate"].includes(token)) return "syntax-variable";
  if (["inline", "heap_allocations", "evaluation", "materialize", "padding", "copies_per_item", "representation", "arity", "order", "count", "elements", "immutable", "preserves_order", "matches_all", "value_after", "value_before"].includes(token)) return "syntax-property";
  return "";
}

function highlight(source: string, language: Language) {
  const tokenPattern = /('[A-Za-z_][\w]*|#[A-Za-z_][\w-]*|@[A-Za-z_][\w]*|[A-Za-z_][\w?!-]*|\d+|"[^"\\]*(?:\\.[^"\\]*)*"|->|=>|::|<=|>=|==|!=|&&|\|\||[{}()[\],.:;=<>|&+*!-])/g;
  const rendered: ReactNode[] = [];
  let lastIndex = 0;
  for (const match of source.matchAll(tokenPattern)) {
    const token = match[0];
    const index = match.index ?? 0;
    if (index > lastIndex) rendered.push(source.slice(lastIndex, index));
    const className = classForToken(token, language);
    rendered.push(className ? <span className={className} key={index}>{token}</span> : token);
    lastIndex = index + token.length;
  }
  if (lastIndex < source.length) rendered.push(source.slice(lastIndex));
  return rendered;
}

export default function App() {
  const [language, setLanguage] = useState<Language>("rust");
  const [layer, setLayer] = useState<Layer>("unified");
  const [selectedLine, setSelectedLine] = useState(1);
  const [tracing, setTracing] = useState(false);
  const [copied, setCopied] = useState(false);

  const visibleLines = programs[language][layer];

  useEffect(() => {
    if (!tracing) return;
    const timer = window.setInterval(() => {
      setSelectedLine((current) => current >= visibleLines.length ? 1 : current + 1);
    }, 900);
    return () => window.clearInterval(timer);
  }, [layer, language, tracing, visibleLines.length]);

  function changeLanguage(nextLanguage: Language) {
    setLanguage(nextLanguage);
    setSelectedLine(1);
  }

  function selectLayer(nextLayer: Layer) {
    setLayer(nextLayer);
    setSelectedLine(1);
  }

  async function copyView() {
    try {
      await navigator.clipboard.writeText(visibleLines.join("\n"));
      setCopied(true);
      window.setTimeout(() => setCopied(false), 1400);
    } catch {
      setCopied(false);
    }
  }

  const activeLanguage = languages.find((item) => item.id === language)!;
  const activeLayer = layerDefinitions.find((item) => item.id === layer)!;
  const currentFile = `${activeLayer.stem}.${activeLanguage.extension}`;

  return (
    <main className="workspace" aria-label="Layered program editor">
      <nav className="layer-nav" aria-label="Program language and layers">
        <div className="language-picker">
          <label className="nav-heading" htmlFor="language-select">LANGUAGE</label>
          <select id="language-select" className="language-select" value={language} onChange={(event) => changeLanguage(event.target.value as Language)}>
            {languages.map((item) => <option key={item.id} value={item.id}>{item.label}</option>)}
          </select>
        </div>
        <div className="layer-list">
          <div className="nav-heading layers-heading">LAYERS</div>
          {layerDefinitions.map((item, index) => (
            <button key={item.id} className={`layer-link ${layer === item.id ? "selected" : ""}`} aria-current={layer === item.id ? "page" : undefined} onClick={() => selectLayer(item.id)}>
              <span className="layer-index">{String(index + 1).padStart(2, "0")}</span>
              <span>{item.label}</span>
            </button>
          ))}
        </div>
      </nav>

      <section className="editor" aria-label={`${activeLanguage.label} ${activeLayer.label} view`}>
        <div className="editor-toolbar">
          <div className="breadcrumb"><span>semantic-demo</span><span>/</span><span>src</span><span>/</span><strong>{currentFile}</strong></div>
          <div className="toolbar-actions">
            <button className={`action-button ${tracing ? "running" : ""}`} aria-label={tracing ? "Stop trace" : "Trace execution"} title="Trace execution" onClick={() => setTracing((value) => !value)}>{tracing ? <span className="trace-pulse" /> : <Play size={13} />}</button>
            <button className="action-button" aria-label="Copy current view" title={copied ? "Copied" : "Copy current view"} onClick={copyView}>{copied ? <Check size={14} /> : <Copy size={14} />}</button>
            <a className="action-button github-link" href="https://github.com/leostera/agentml" target="_blank" rel="noreferrer" aria-label="Open the agentml GitHub repository" title="GitHub repository"><svg viewBox="0 0 24 24" width="14" height="14" aria-hidden="true"><path fill="currentColor" d="M12 .75a11.25 11.25 0 0 0-3.56 21.92c.56.1.77-.24.77-.54v-2.1c-3.14.68-3.8-1.33-3.8-1.33-.51-1.3-1.25-1.64-1.25-1.64-1.03-.7.08-.69.08-.69 1.14.08 1.74 1.17 1.74 1.17 1.02 1.74 2.67 1.24 3.32.95.1-.74.4-1.24.73-1.53-2.51-.28-5.15-1.25-5.15-5.58 0-1.23.44-2.24 1.17-3.03-.12-.29-.51-1.44.11-3 0 0 .96-.3 3.09 1.16a10.74 10.74 0 0 1 5.63 0c2.14-1.45 3.09-1.16 3.09-1.16.62 1.56.23 2.71.11 3 .73.79 1.17 1.8 1.17 3.03 0 4.34-2.65 5.3-5.17 5.57.41.35.77 1.04.77 2.1v3.08c0 .3.2.65.77.54A11.25 11.25 0 0 0 12 .75Z" /></svg></a>
          </div>
        </div>

        <div className="code-editor">
          <div className={`code-content language-${language}`}>
            {visibleLines.map((source, index) => {
              const line = index + 1;
              return <button key={`${language}-${layer}-${line}`} className={`code-line ${selectedLine === line ? "selected" : ""}`} onClick={() => setSelectedLine(line)} aria-label={`Select line ${line}`}>
                <span className="line-number">{String(line).padStart(2, "0")}</span>
                <code>{highlight(source, language)}</code>
              </button>;
            })}
          </div>
          <div className="statusbar"><span><i /> {activeLanguage.label} · {activeLayer.label}</span><span>Ln {selectedLine}, Col 1</span><span>UTF-8</span></div>
        </div>
      </section>
    </main>
  );
}
