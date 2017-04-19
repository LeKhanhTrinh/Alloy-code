module simple_example

// A file system object in the file system
sig FSObject { parent: lone Dir }

// A directory in the file system
sig Dir extends FSObject { contents: set FSObject }

// A file in the file system
sig File extends FSObject { }

// A directory is the parent of its contents
fact { all d: Dir, o: d.contents | o.parent = d }

// All file system objects are either files or directories
fact { File + Dir = FSObject }

// Every fs object is in at most one directory
assert oneLocation { 
	all o: FSObject | lone d: Dir | 
		o in d.contents 
}

check oneLocation
