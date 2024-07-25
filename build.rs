use std::{
    collections::HashSet,
    env,
    error::Error,
    fs::{read_dir, File},
    io::{BufWriter, Write as _},
    path::PathBuf,
};

// const VALID_ANGLE_BYTES: &[u8] = b"wedsaq";

fn main() {
    build_patterns().unwrap();
}

fn build_patterns() -> Result<(), Box<dyn Error>> {
    let mut variants = Vec::new();
    let mut seen_ids = HashSet::new();
    let mut parse_table = vec![
        ("hexpattern".to_owned(), 1u64.wrapping_neg()),
        ("numericalreflection".to_owned(), 2u64.wrapping_neg()),
        ("bookkeeper'sgambit".to_owned(), 3u64.wrapping_neg()),
        ("null".to_owned(), 4u64.wrapping_neg()),
    ];

    println!("cargo::rerun-if-changed=patterns");
    let mut record = csv::StringRecord::new();
    for file in read_dir("patterns/")? {
        let file = file.unwrap();

        if !file.path().extension().is_some_and(|ext| ext == "csv") {
            continue;
        }

        // csv: variant,id,angles,direction,great,name,parse

        let mut reader = csv::Reader::from_path(file.path())?;
        while reader.read_record(&mut record)? {
            if !seen_ids.insert(record[1].to_owned()) {
                continue;
            }

            parse_table.push((record[6].to_owned(), u64::try_from(variants.len()).unwrap()));

            variants.push(record[0].to_owned());
        }
    }

    parse_table.sort_unstable_by(|(k1, _), (k2, _)| Ord::cmp(k1, k2));

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());

    {
        let mut parse_fst =
            fst::MapBuilder::new(BufWriter::new(File::create(out_dir.join("pattern_parse_table"))?))?;

        parse_fst.extend_iter(parse_table)?;

        parse_fst.finish()?;
    }

    let mut source_file = BufWriter::new(File::create(out_dir.join("patterns.rs"))?);

    write!(
        &mut source_file,
        concat!(
            "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\n",
            "pub enum SimplePattern {{\n",
        )
    )?;
    for (i, s) in variants.iter().enumerate() {
        writeln!(&mut source_file, "    {} = {},", s, i)?;
    }
    writeln!(&mut source_file, "}}")?;

    writeln!(&mut source_file)?;

    write!(
        &mut source_file,
        concat!(
            "impl ::std::convert::TryFrom<u64> for SimplePattern {{\n",
            "    type Error = ();\n",
            "    fn try_from(v: u64) -> Result<Self, ()> {{\n",
            "        Ok(match v {{\n",
        )
    )?;
    for (i, s) in variants.iter().enumerate() {
        writeln!(&mut source_file, "            {} => Self::{},", i, s)?;
    }
    write!(
        &mut source_file,
        concat!(
            "            _ => return Err(()),\n",
            "        }})\n",
            "    }}\n",
            "}}\n",
        )
    )?;

    writeln!(&mut source_file)?;

    write!(
        &mut source_file,
        concat!(
            "impl ::std::convert::From<SimplePattern> for usize {{\n",
            "    fn from(v: SimplePattern) -> usize {{\n",
            "        match v {{\n",
        )
    )?;
    for (i, s) in variants.iter().enumerate() {
        writeln!(
            &mut source_file,
            "            SimplePattern::{} => {}usize,",
            s, i
        )?;
    }
    write!(
        &mut source_file,
        concat!("        }}\n", "    }}\n", "}}\n")
    )?;

    Ok(())
}
