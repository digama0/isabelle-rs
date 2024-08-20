#[derive(Debug)]
pub enum Entry<'input> {
  ChapterDef,
  Chapter,
  Session { sess: &'input str, parent: Option<&'input str> },
}
