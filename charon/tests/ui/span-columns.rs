//@ known-failure
// Errors after multibyte, wide and tab characters on their line.
/* é 日本 */ #[charon::rename("")] pub type Wide = ();
	#[charon::rename("")] pub type Tab = ();
#[charon::rename("🦀")] pub type Crab = ();
