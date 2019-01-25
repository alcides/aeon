class Box {
  
  public Integer v = 0;
  
  public Box(int i) {
    v = i;
  }
  
  public String toString() {
    if (v == 5)
      return "Box Open";
    return "Box Closed ["+v+"] + " + Box.isOpen(this) + "/" + Box.isValid(this);
  }
  
  
  
  public static Box pickBox() {
    return new Box(0);
  }
  
  public static Box startCode(Box b) {
    if (b.v == 0) return new Box(1);
    return new Box(10);
  }
  
  public static Box advance(Box b) {
    if (b.v >= 1 && b.v < 4 )
      return new Box(b.v+1);
    return new Box(10);
  }
  
  public static Box endCode(Box b) {
    if (b.v == 4) return new Box(5);
    if (b.v > 0) return new Box(6);
    return new Box(10);
  }
  
  public static Boolean isOpen(Box b) {
    return b.v == 5;
  }
  
  public static Boolean isValid(Box b) {
    return b.v != 10;
  }
  
  public static void main(String[] args) {
    Box b = Box.pickBox();
    System.out.println(b);
    b = Box.advance(b);
    System.out.println(b);
    b = Box.endCode(b);
    System.out.println(b);
    
    
    b = Box.pickBox();
    b = Box.startCode(b);
    b = Box.advance(b);
    b = Box.advance(b);
    b = Box.advance(b);
    b = Box.endCode(b);
    System.out.println(b);
  }
}