//! PubMed verification toolkit (NCBI E-utilities) — Rust port.
//!
//! Usage:
//!   cargo run --bin pubmed_verify -- search "<query>" [--max N]
//!   cargo run --bin pubmed_verify -- verify "<term1>" "<term2>"
//!   cargo run --bin pubmed_verify -- batch
//!
//! NCBI E-utilities, no API key required (polite 0.4 s between requests).

use std::collections::BTreeMap;
use std::io::Read;
use std::thread;
use std::time::Duration;

const BASE: &str = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils";

#[derive(Clone, Debug, Default)]
struct Summary {
    title: String,
    journal: String,
    pubdate: String,
    authors: String,
    doi: String,
}

fn get_json(url: &str) -> serde_json::Value {
    for attempt in 0..3 {
        match ureq::get(url).timeout(Duration::from_secs(30)).call() {
            Ok(resp) => {
                let mut body = String::new();
                if resp.into_reader().read_to_string(&mut body).is_ok() {
                    if let Ok(v) = serde_json::from_str(&body) {
                        return v;
                    }
                }
            }
            Err(_) => {
                if attempt == 2 {
                    break;
                }
                thread::sleep(Duration::from_secs(1));
            }
        }
    }
    serde_json::Value::Null
}

fn esearch(term: &str, retmax: usize) -> Vec<String> {
    let url = format!(
        "{}/esearch.fcgi?db=pubmed&retmax={}&retmode=json&term={}",
        BASE,
        retmax,
        url_encode(term)
    );
    let v = get_json(&url);
    v.pointer("/esearchresult/idlist")
        .and_then(|a| a.as_array())
        .map(|a| {
            a.iter()
                .filter_map(|x| x.as_str().map(String::from))
                .collect()
        })
        .unwrap_or_default()
}

fn esummary(pmids: &[String]) -> BTreeMap<String, Summary> {
    if pmids.is_empty() {
        return BTreeMap::new();
    }
    let url = format!(
        "{}/esummary.fcgi?db=pubmed&retmode=json&id={}",
        BASE,
        pmids.join(",")
    );
    let v = get_json(&url);
    let mut out = BTreeMap::new();
    if let Some(result) = v.get("result").and_then(|r| r.as_object()) {
        for (pid, info) in result {
            if pid == "uids" {
                continue;
            }
            let mut s = Summary::default();
            if let Some(t) = info.get("title").and_then(|x| x.as_str()) {
                s.title = t.to_string();
            }
            if let Some(j) = info
                .get("fulljournalname")
                .and_then(|x| x.as_str())
                .or_else(|| info.get("source").and_then(|x| x.as_str()))
            {
                s.journal = j.to_string();
            }
            if let Some(d) = info.get("pubdate").and_then(|x| x.as_str()) {
                s.pubdate = d.to_string();
            }
            if let Some(authors) = info.get("authors").and_then(|x| x.as_array()) {
                s.authors = authors
                    .iter()
                    .take(8)
                    .filter_map(|a| a.get("name").and_then(|n| n.as_str()))
                    .collect::<Vec<_>>()
                    .join(", ");
            }
            if let Some(ids) = info.get("articleids").and_then(|x| x.as_array()) {
                for id in ids {
                    if id.get("idtype").and_then(|x| x.as_str()) == Some("doi") {
                        if let Some(d) = id.get("value").and_then(|x| x.as_str()) {
                            s.doi = d.to_string();
                        }
                    }
                }
            }
            out.insert(pid.clone(), s);
        }
    }
    out
}

fn url_encode(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join("+")
}

fn search(term: &str, retmax: usize) -> BTreeMap<String, Summary> {
    let ids = esearch(term, retmax);
    thread::sleep(Duration::from_millis(400));
    esummary(&ids)
}

fn markdown(rows: &BTreeMap<String, Summary>) -> String {
    let mut out = String::from("| PMID | Year | Title | Journal | Authors | DOI |\n");
    out.push_str("|---|---|---|---|---|---|\n");
    for (pid, s) in rows {
        let year = s.pubdate.chars().take(4).collect::<String>();
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} |\n",
            pid,
            year,
            truncate(&s.title, 90),
            truncate(&s.journal, 40),
            truncate(&s.authors, 60),
            s.doi
        ));
    }
    out
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        s.chars().take(n).collect()
    }
}

const REFS: &[(&str, &str)] = &[
    (
        "Rujano 2006",
        "Rujano polarised asymmetric inheritance accumulated protein damage",
    ),
    (
        "Aguilaniu 2003",
        "Aguilaniu asymmetric inheritance oxidatively damaged proteins cytokinesis",
    ),
    (
        "Erjavec 2007",
        "Erjavec Sir2 damaged proteins segregation aging",
    ),
    (
        "Katajisto 2015",
        "Katajisto asymmetric apportioning aged mitochondria daughter cells stemness",
    ),
    (
        "Moore 2015",
        "Moore lateral diffusion barrier endoplasmic reticulum asymmetric neural stem cells",
    ),
    (
        "Yamashita 2007",
        "Yamashita asymmetric inheritance mother versus daughter centrosome stem cell division",
    ),
    (
        "Wang 2009",
        "Wang asymmetric centrosome inheritance maintains neural progenitors neocortex",
    ),
    (
        "Fong 2016",
        "Fong 53BP1 USP28 p53 centrosome loss mitotic duration G1 arrest",
    ),
    (
        "Meitinger 2016",
        "Meitinger 53BP1 USP28 p53 extended mitotic duration",
    ),
    (
        "Meitinger 2020",
        "Meitinger TRIM37 CEP192 acentrosomal spindle PLK4",
    ),
    (
        "Sparr 2025",
        "Sparr Meitinger mitotic surveillance pathway review",
    ),
    (
        "Bollineni 2014",
        "Bollineni carbonylation HeLa oxidation sites",
    ),
    (
        "Koehrer 2023",
        "Koehrer plasma cells centriole elongation aging",
    ),
];

const CHECKS: &[(&str, &str)] = &[
    (
        "segregation efficiency declines with age",
        "age related decline asymmetric segregation damaged proteins stem cells efficiency",
    ),
    (
        "redundant quality-control backups",
        "redundancy protein quality control mechanisms aging proteostasis network",
    ),
    (
        "division as entropy export",
        "cell division eliminates damaged proteins asymmetric inheritance daughter",
    ),
    (
        "centriole not turned over / non-renewable",
        "centriole structural protein long-lived stable non-exchangeable scaffold",
    ),
    (
        "proteostasis declines with age",
        "proteostasis decline aging proteome quality control",
    ),
    (
        "old centriole to stem-cell daughter",
        "centrosome age asymmetric stem cell division mother centriole inheritance",
    ),
    (
        "mitochondria: old to differentiating daughter",
        "mitochondria segregation old damaged to differentiating daughter stem cells",
    ),
    (
        "autophagy/QC declines with age",
        "autophagy decline with age proteostasis cellular quality control",
    ),
];

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        println!("usage: search <term> [--max N] | verify <t1> <t2>... | batch");
        return;
    }
    match args[0].as_str() {
        "search" => {
            let term = args.get(1).cloned().unwrap_or_default();
            let mut mx = 5usize;
            if let Some(i) = args.iter().position(|a| a == "--max") {
                if let Some(v) = args.get(i + 1).and_then(|v| v.parse().ok()) {
                    mx = v;
                }
            }
            println!("{}", markdown(&search(&term, mx)));
        }
        "verify" => {
            for term in args.iter().skip(1) {
                println!("\n### {}\n", term);
                println!("{}", markdown(&search(term, 3)));
            }
        }
        "batch" => {
            println!("# Verified references (PubMed, NCBI E-utilities, Rust)\n");
            for (label, term) in REFS {
                println!("\n## {} — search: {}\n", label, term);
                println!("{}", markdown(&search(term, 3)));
                thread::sleep(Duration::from_millis(400));
            }
            println!("\n\n# Assumption checks (model vs literature)\n");
            for (label, term) in CHECKS {
                println!("\n## {}\n", label);
                println!("{}", markdown(&search(term, 4)));
                thread::sleep(Duration::from_millis(400));
            }
        }
        _ => println!("unknown mode: {}", args[0]),
    }
}
