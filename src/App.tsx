import { useEffect, useState, type ReactNode } from "react";
import { Check, Copy, Play } from "lucide-react";

type Layer = "unified" | "code" | "lifetimes" | "types" | "invariants" | "performance";
type LayerDefinition = { id: Layer; label: string; file: string };

const layers: LayerDefinition[] = [
  { id: "unified", label: "Unified", file: "foo.unified.rs" },
  { id: "code", label: "Code", file: "foo.rs" },
  { id: "lifetimes", label: "Lifetimes", file: "foo.lifetimes.rs" },
  { id: "types", label: "Types", file: "foo.types.rs" },
  { id: "invariants", label: "Invariants", file: "foo.invariants.rs" },
  { id: "performance", label: "Performance", file: "foo.performance.rs" },
];

const sourceForCopy = `fn rank<'query, 'docs>(\n    query: &'query str,\n    docs: &'docs [Document],\n) -> impl Iterator<Item = &'docs Document> + 'query + 'docs {\n    let candidates: std::slice::Iter<'docs, Document> = docs.iter();\n    candidates.filter(move |doc: &&'docs Document| doc.title().contains(query))\n}`;

function lineCount(layer: Layer) {
  if (layer === "unified") return 29;
  if (layer === "code") return 4;
  if (layer === "lifetimes") return 7;
  if (layer === "types") return 6;
  if (layer === "invariants") return 14;
  return 14;
}

function languageFor(layer: Layer) {
  if (layer === "unified") return "Unified surface";
  if (layer === "invariants") return "Invariant DSL";
  if (layer === "performance") return "Performance DSL";
  if (layer === "types") return "Type projection";
  return "Rust";
}

export default function App() {
  const [layer, setLayer] = useState<Layer>("unified");
  const [selectedLine, setSelectedLine] = useState(1);
  const [tracing, setTracing] = useState(false);
  const [copied, setCopied] = useState(false);

  useEffect(() => {
    if (!tracing) return;
    const lastLine = lineCount(layer);
    const timer = window.setInterval(() => {
      setSelectedLine((current) => current >= lastLine ? 1 : current + 1);
    }, 900);
    return () => window.clearInterval(timer);
  }, [layer, tracing]);

  function selectLayer(nextLayer: Layer) {
    setLayer(nextLayer);
    setSelectedLine(1);
  }

  async function copySource() {
    try {
      await navigator.clipboard.writeText(sourceForCopy);
      setCopied(true);
      window.setTimeout(() => setCopied(false), 1400);
    } catch {
      setCopied(false);
    }
  }

  const currentFile = layers.find((item) => item.id === layer)?.file ?? "foo.unified.rs";

  return (
    <main className="workspace" aria-label="Layered Rust editor">
      <nav className="layer-nav" aria-label="Program layers">
        <div className="nav-heading">LAYERS</div>
        {layers.map((item, index) => (
          <button key={item.id} className={`layer-link ${layer === item.id ? "selected" : ""}`} aria-current={layer === item.id ? "page" : undefined} onClick={() => selectLayer(item.id)}>
            <span className="layer-index">{String(index + 1).padStart(2, "0")}</span>
            <span>{item.label}</span>
          </button>
        ))}
      </nav>

      <section className="editor" aria-label={`${layers.find((item) => item.id === layer)?.label} view`}>
        <div className="editor-toolbar">
          <div className="breadcrumb"><span>semantic-demo</span><span>/</span><span>src</span><span>/</span><strong>{currentFile}</strong></div>
          <div className="toolbar-actions">
            <button className={`action-button ${tracing ? "running" : ""}`} aria-label={tracing ? "Stop trace" : "Trace execution"} title="Trace execution" onClick={() => setTracing((value) => !value)}>{tracing ? <span className="trace-pulse" /> : <Play size={13} />}</button>
            <button className="action-button" aria-label="Copy Rust source" title={copied ? "Copied" : "Copy source"} onClick={copySource}>{copied ? <Check size={14} /> : <Copy size={14} />}</button>
          </div>
        </div>

        <div className="code-editor">
          <div className="code-content">
            {Array.from({ length: lineCount(layer) }, (_, index) => {
              const line = index + 1;
              return <CodeLine key={`${layer}-${line}`} line={line} selected={selectedLine === line} onClick={() => setSelectedLine(line)}>
                {renderLine(layer, line)}
              </CodeLine>;
            })}
          </div>
          <div className="statusbar"><span><i /> {languageFor(layer)}</span><span>Ln {selectedLine}, Col 1</span><span>UTF-8</span></div>
        </div>
      </section>
    </main>
  );
}

function CodeLine({ line, selected, children, onClick }: { line: number; selected: boolean; children: ReactNode; onClick: () => void }) {
  return <button className={`code-line ${selected ? "selected" : ""}`} onClick={onClick} aria-label={`Select line ${line}`}>
    <span className="line-number">{String(line).padStart(2, "0")}</span>
    <code>{children}</code>
  </button>;
}

function renderLine(layer: Layer, line: number) {
  if (layer === "unified") return renderUnifiedLine(line);
  if (layer === "code") return renderCodeLine(line);
  if (layer === "lifetimes") return renderLifetimeLine(line);
  if (layer === "types") return renderTypedLine(line);
  if (layer === "invariants") return renderInvariantLine(line);
  return renderPerformanceLine(line);
}

function renderCodeLine(line: number) {
  switch (line) {
    case 1: return <><Keyword>fn</Keyword> <FunctionName>rank</FunctionName>(<Parameter>query</Parameter>, <Parameter>docs</Parameter>) &#123;</>;
    case 2: return <><Indent />let <Variable>candidates</Variable> = <Variable>docs</Variable>.<Method>iter</Method>();</>;
    case 3: return <><Indent /><Variable>candidates</Variable>.<Method>filter</Method>(|<Parameter>doc</Parameter>| <Variable>doc</Variable>.<Method>title</Method>().<Method>contains</Method>(<Variable>query</Variable>))</>;
    default: return <>&#125;</>;
  }
}

function renderLifetimeLine(line: number) {
  switch (line) {
    case 1: return <><Keyword>fn</Keyword> <FunctionName>rank</FunctionName>&lt;<Lifetime>'query</Lifetime>, <Lifetime>'docs</Lifetime>&gt;(</>;
    case 2: return <><Indent /><Parameter>query</Parameter>: &amp;<Lifetime>'query</Lifetime> <TypeName>str</TypeName>,</>;
    case 3: return <><Indent /><Parameter>docs</Parameter>: &amp;<Lifetime>'docs</Lifetime> [<TypeName>Document</TypeName>],</>;
    case 4: return <><Indent />) -&gt; <Keyword>impl</Keyword> <TypeName>Iterator</TypeName>&lt;Item = &amp;<Lifetime>'docs</Lifetime> <TypeName>Document</TypeName>&gt; + <Lifetime>'query</Lifetime> + <Lifetime>'docs</Lifetime> &#123;</>;
    case 5: return <><Indent /><Keyword>let</Keyword> <Variable>candidates</Variable>: <TypeName>std::slice::Iter</TypeName>&lt;<Lifetime>'docs</Lifetime>, <TypeName>Document</TypeName>&gt; = <Variable>docs</Variable>.<Method>iter</Method>();</>;
    case 6: return <><Indent /><Variable>candidates</Variable>.<Method>filter</Method>(<Keyword>move</Keyword> |<Parameter>doc</Parameter>: &amp;&amp;<Lifetime>'docs</Lifetime> <TypeName>Document</TypeName>| <Variable>doc</Variable>.<Method>title</Method>().<Method>contains</Method>(<Variable>query</Variable>))</>;
    default: return <>&#125;</>;
  }
}

function renderTypedLine(line: number) {
  switch (line) {
    case 1: return <><Keyword>type</Keyword> <TypeName>DocumentRef</TypeName> = &amp;<TypeName>Document</TypeName></>;
    case 2: return <><Keyword>fn</Keyword> <FunctionName>rank</FunctionName>(<Parameter>query</Parameter>: &amp;<TypeName>str</TypeName>, <Parameter>docs</Parameter>: &amp;[<TypeName>Document</TypeName>]) -&gt; <TypeName>Iterator</TypeName>&lt;<TypeName>DocumentRef</TypeName>&gt;</>;
    case 3: return <><Keyword>let</Keyword> <Variable>candidates</Variable>: <TypeName>Iter</TypeName>&lt;<TypeName>DocumentRef</TypeName>&gt; = <Method>iter</Method>(<Variable>docs</Variable>)</>;
    case 4: return <><Keyword>let</Keyword> <Variable>predicate</Variable>: <TypeName>DocumentRef</TypeName> → <TypeName>bool</TypeName> = <Method>matches_title</Method>(<Variable>query</Variable>)</>;
    case 5: return <><Keyword>let</Keyword> <Variable>matching</Variable>: <TypeName>Filter</TypeName>&lt;<TypeName>Iter</TypeName>&lt;<TypeName>DocumentRef</TypeName>&gt;, <TypeName>Fn</TypeName>&lt;<TypeName>DocumentRef</TypeName>, <TypeName>bool</TypeName>&gt;&gt; = <Method>filter</Method>(<Variable>candidates</Variable>, <Variable>predicate</Variable>)</>;
    default: return <><Keyword>return</Keyword> <Variable>matching</Variable></>;
  }
}

function renderInvariantLine(line: number) {
  switch (line) {
    case 1: return <><Invariant>invariant</Invariant> <TypeName>rank</TypeName> &#123;</>;
    case 2: return <><Indent /><Invariant>arity</Invariant>(rank) == <NumberToken>2</NumberToken></>;
    case 3: return <><Indent /><Invariant>result</Invariant>(rank, query, docs) ⊆ docs</>;
    case 4: return <><Indent />∀ doc ∈ result: <Invariant>matches</Invariant>(doc.title, query)</>;
    case 5: return <><Indent /><Invariant>order</Invariant>(result) = <Invariant>order</Invariant>(docs filtered by query)</>;
    case 6: return <>&#125;</>;
    case 7: return <><Invariant>invariant</Invariant> <TypeName>query</TypeName> &#123;</>;
    case 8: return <><Indent /><Invariant>immutable</Invariant>(query)</>;
    case 9: return <><Indent /><Invariant>value_after</Invariant>(rank, query) = <Invariant>value_before</Invariant>(rank, query)</>;
    case 10: return <>&#125;</>;
    case 11: return <><Invariant>invariant</Invariant> <TypeName>candidates</TypeName> &#123;</>;
    case 12: return <><Indent /><Invariant>count</Invariant>(candidates) = <Invariant>count</Invariant>(docs) ∧ <Invariant>order</Invariant>(candidates) = <Invariant>order</Invariant>(docs)</>;
    case 13: return <><Indent /><Invariant>elements</Invariant>(candidates) ⊆ docs</>;
    default: return <>&#125;</>;
  }
}

function renderPerformanceLine(line: number) {
  switch (line) {
    case 1: return <><Plan>plan</Plan> <TypeName>rank</TypeName> &#123;</>;
    case 2: return <><Indent /><Property>inline</Property>(<FunctionName>rank</FunctionName>) = <Value>auto</Value></>;
    case 3: return <><Indent /><Property>return</Property> = <Value>lazy_iterator</Value></>;
    case 4: return <><Indent /><Property>heap_allocations</Property> = <NumberToken>0</NumberToken></>;
    case 5: return <>&#125;</>;
    case 6: return <><Plan>plan</Plan> <TypeName>candidates</TypeName> &#123;</>;
    case 7: return <><Indent /><Property>representation</Property> = <Value>slice_iterator</Value></>;
    case 8: return <><Indent /><Property>copies_per_item</Property> = <NumberToken>0</NumberToken></>;
    case 9: return <><Indent /><Property>padding</Property>(<Variable>candidates</Variable>) = <Value>none</Value></>;
    case 10: return <>&#125;</>;
    case 11: return <><Plan>plan</Plan> <TypeName>matching</TypeName> &#123;</>;
    case 12: return <><Indent /><Property>evaluation</Property> = <Value>on_consume</Value></>;
    case 13: return <><Indent /><Property>materialize</Property> = <Value>false</Value></>;
    default: return <>&#125;</>;
  }
}

function renderUnifiedLine(line: number) {
  switch (line) {
    case 1: return <><span className="syntax-attribute">#[perf</span>(<Property>inline</Property>(<FunctionName>rank</FunctionName>) = <Value>auto</Value>, <Property>heap_allocations</Property> = <NumberToken>0</NumberToken>, <Property>evaluation</Property> = <Value>lazy</Value>)<span className="syntax-attribute">]</span></>;
    case 2: return <><span className="syntax-attribute">#[perf</span>(<Property>materialize</Property> = <Value>false</Value>, <Property>padding</Property>(<Variable>candidates</Variable>) = <Value>none</Value>, <Property>copies_per_item</Property> = <NumberToken>0</NumberToken>)<span className="syntax-attribute">]</span></>;
    case 3: return <><Keyword>type</Keyword> <TypeName>Predicate</TypeName>&lt;<Lifetime>'query</Lifetime>, <Lifetime>'docs</Lifetime>&gt; = <TypeName>FnMut</TypeName>(&amp;&amp;<Lifetime>'docs</Lifetime> <TypeName>Document</TypeName>) -&gt; <TypeName>bool</TypeName> + <Lifetime>'query</Lifetime>;</>;
    case 4: return <><Keyword>fn</Keyword> <FunctionName>rank</FunctionName>&lt;<Lifetime>'query</Lifetime>, <Lifetime>'docs</Lifetime>&gt;(</>;
    case 5: return <><Indent /><Keyword>immutable</Keyword> <Parameter>query</Parameter>: &amp;<Lifetime>'query</Lifetime> <TypeName>str</TypeName>,</>;
    case 6: return <><Indent /><Parameter>docs</Parameter>: &amp;<Lifetime>'docs</Lifetime> [<TypeName>Document</TypeName>],</>;
    case 7: return <><Indent />) -&gt; <Keyword>impl</Keyword> <TypeName>Iterator</TypeName>&lt;Item = &amp;<Lifetime>'docs</Lifetime> <TypeName>Document</TypeName>&gt; + <Lifetime>'query</Lifetime> + <Lifetime>'docs</Lifetime></>;
    case 8: return <><Keyword>ensures</Keyword> &#123;</>;
    case 9: return <><Indent /><Invariant>arity</Invariant>(<FunctionName>rank</FunctionName>) = <NumberToken>2</NumberToken>;</>;
    case 10: return <><Indent /><Invariant>result</Invariant> ⊆ <Variable>docs</Variable>;</>;
    case 11: return <><Indent /><Invariant>matches_all</Invariant>(<Invariant>result</Invariant>, <Variable>query</Variable>);</>;
    case 12: return <><Indent /><Invariant>preserves_order</Invariant>(<Invariant>result</Invariant>, <Variable>docs</Variable>);</>;
    case 13: return <><Indent /><Invariant>value_after</Invariant>(<Variable>query</Variable>) = <Invariant>value_before</Invariant>(<Variable>query</Variable>);</>;
    case 14: return <>&#125;</>;
    case 15: return <>&#123;</>;
    case 16: return <><Indent /><Keyword>let</Keyword> <Variable>candidates</Variable>: <TypeName>Iter</TypeName>&lt;<Lifetime>'docs</Lifetime>, <TypeName>Document</TypeName>&gt; = <Variable>docs</Variable>.<Method>iter</Method>();</>;
    case 17: return <><Indent /><Keyword>invariant</Keyword> &#123;</>;
    case 18: return <><Indent level={2} /><Invariant>count</Invariant>(<Variable>candidates</Variable>) = <Invariant>count</Invariant>(<Variable>docs</Variable>);</>;
    case 19: return <><Indent level={2} /><Invariant>order</Invariant>(<Variable>candidates</Variable>) = <Invariant>order</Invariant>(<Variable>docs</Variable>);</>;
    case 20: return <><Indent level={2} /><Invariant>elements</Invariant>(<Variable>candidates</Variable>) ⊆ <Variable>docs</Variable>;</>;
    case 21: return <><Indent />&#125;;</>;
    case 22: return <><Indent /><Keyword>let</Keyword> <Variable>matching</Variable>: <TypeName>Filter</TypeName>&lt;</>;
    case 23: return <><Indent level={2} /><TypeName>Iter</TypeName>&lt;<Lifetime>'docs</Lifetime>, <TypeName>Document</TypeName>&gt;,</>;
    case 24: return <><Indent level={2} /><TypeName>Predicate</TypeName>&lt;<Lifetime>'query</Lifetime>, <Lifetime>'docs</Lifetime>&gt;</>;
    case 25: return <><Indent />&gt; = <Variable>candidates</Variable>.<Method>filter</Method>(<Keyword>move</Keyword> |<Parameter>doc</Parameter>: &amp;&amp;<Lifetime>'docs</Lifetime> <TypeName>Document</TypeName>| -&gt; <TypeName>bool</TypeName> &#123;</>;
    case 26: return <><Indent level={2} /><Variable>doc</Variable>.<Method>title</Method>().<Method>contains</Method>(<Variable>query</Variable>)</>;
    case 27: return <><Indent />&#125;);</>;
    case 28: return <><Indent /><Variable>matching</Variable></>;
    default: return <>&#125;</>;
  }
}

function Keyword({ children }: { children: ReactNode }) { return <span className="syntax-keyword">{children}</span>; }
function FunctionName({ children }: { children: ReactNode }) { return <span className="syntax-function">{children}</span>; }
function Parameter({ children }: { children: ReactNode }) { return <span className="syntax-parameter">{children}</span>; }
function Variable({ children }: { children: ReactNode }) { return <span className="syntax-variable">{children}</span>; }
function Method({ children }: { children: ReactNode }) { return <span className="syntax-method">{children}</span>; }
function TypeName({ children }: { children: ReactNode }) { return <span className="syntax-type">{children}</span>; }
function Lifetime({ children }: { children: ReactNode }) { return <span className="syntax-lifetime">{children}</span>; }
function Invariant({ children }: { children: ReactNode }) { return <span className="syntax-invariant">{children}</span>; }
function Plan({ children }: { children: ReactNode }) { return <span className="syntax-invariant">{children}</span>; }
function Property({ children }: { children: ReactNode }) { return <span className="syntax-property">{children}</span>; }
function Value({ children }: { children: ReactNode }) { return <span className="syntax-value">{children}</span>; }
function NumberToken({ children }: { children: ReactNode }) { return <span className="syntax-number">{children}</span>; }
function Indent({ level = 1 }: { level?: number }) { return <span className="indent" aria-hidden="true" style={{ width: `${level * 4}ch` }} />; }
