class FileH {
  
  public boolean open = false;
  public int contents = 0;


  public FileH() {
  }  
  
  public FileH(int contents, boolean open) {
    this.contents = contents;
    this.open = open;
  }
  
  public String toString() {
    return "FH: open=" + open;
  }
  
  public static FileH mkFileH() {
    return new FileH();
  }
  
  public static FileH open(FileH f) {
    return new FileH(f.contents, true);
  }
  
  public static FileH close(FileH f) {
    return new FileH(f.contents, false);
  }
  
  public static Integer read(FileH f) {
    if (f.open) return f.contents;
    else throw new RuntimeException("Failed");
  }
  
  public static FileH write(FileH f, Integer c) {
    if (f.open) {
      return new FileH(c, true);
    } else throw new RuntimeException("Failed");
  }
  
  
  public static void main(String[] args) {
    FileH f1 = mkFileH();
      
    f1 = FileH.open(f1);
    f1 = write(f1, 123);
    f1 = FileH.close(f1);
    
    f1 = FileH.open(f1);
    
    System.out.println(FileH.read(f1));
    
    
    
  }
}