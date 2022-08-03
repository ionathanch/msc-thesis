$pdf_mode = 4;
$lualatex = 'lualatex --shell-escape --interaction=nonstopmode --synctex=1 %O %S';
$bibtex_use = 2;
$success_cmd = 'latexmk --jobname=%R -c; [ ! -f thesis.pdf ] || mv thesis.pdf ubc_2022_november_chan_jonathan.pdf';
push @generated_exts, 'brf';
@default_files = ('thesis.tex');