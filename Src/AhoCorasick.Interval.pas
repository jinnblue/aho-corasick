{ *************************************************************************** }
{ 描 述：线段树 }
{ 功 能：用于修饰匹配结果,例如在[ushers]中匹配she,he时结果会重叠,这棵线段树对
  匹配结果(一系列区间)进行索引,能够在log(n)时间内判断两个区间是否重叠
  {作 者：賓虎  2016.07 }
{ 参 考: www.hankcs.com/program/algorithm/implementation-and-analysis-of-aho-corasick-algorithm-in-java.html
  {*************************************************************************** }
unit AhoCorasick.Interval;

interface

uses
  System.Classes, System.Generics.Collections;

type
  { 区间 }
  TInterval = class(TObject)
  private
    FStart: Integer; // 起点
    FEnd: Integer;   // 终点
  public
    constructor Create(const AStart, AEnd: Integer);

    function Equals(AOther: TObject): Boolean; override;
    function Size: Integer;
    function ToString: string; override;
    function OverlapsWith(const AOther: TInterval): Boolean; overload; // 是否与另一区间交叉重叠
    function OverlapsWith(const APoint: Integer): Boolean; overload; // 区间是否覆盖了某点
    property GetStart: Integer read FStart;
    property GetEnd: Integer read FEnd;
  end;

  { 一个模式串匹配结果 }
  TEmit = class(TInterval)
  private
    FKeyword: string;
  public
    constructor Create(const AStart, AEnd: Integer; const AKeyword: string);
    function ToString: string; override;
    property Keyword: string read FKeyword;
  end;

  { 线段树上面的节点，实际上是一些区间的集合，并且按中点维护了两个节点 }
  TIntervalNode = class(TObject)
  private type
    TDirection = (LEFT, RIGHT);
  private
    FLeft: TIntervalNode;         // 区间集合的最左端,初始化为nil
    FRight: TIntervalNode;        // 最右端
    FPoint: Integer;              // 中点
    FIntervals: TList<TInterval>; // 区间集合
    FInited: Boolean;
    procedure Initial; inline;
  protected
    procedure AddToOverlaps(const AItl: TInterval; AOverlaps, ANewOverlaps: TList<TInterval>);
    function CheckForOverlaps(const AItl: TInterval; const ADir: TDirection): TList<TInterval>;
    function CheckForOverlapsToTheLeft(const AItl: TInterval): TList<TInterval>;
    function CheckForOverlapsToTheRight(const AItl: TInterval): TList<TInterval>;
    class function FindOverlappingRanges(const aNode: TIntervalNode; const AItl: TInterval)
      : TList<TInterval>;
  public
    constructor Create(const AItls: TList<TInterval>);
    destructor Destroy; override;
    function CalcMedian(const AItls: TList<TInterval>): Integer; // 计算中点
    function FindOverlaps(const AItl: TInterval): TList<TInterval>; // 寻找与FIntervals有重叠的区间
  end;

  { 线段树，用于检查区间重叠 }
  TIntervalTree = class(TObject)
  private
    FRootNode: TIntervalNode; // 根节点
    FOverlapResult: TList<TInterval>;
  public
    constructor Create(const AItls: TList<TInterval>);
    destructor Destroy; override;

    procedure RemoveOverlaps(var AItls: TList<TInterval>); // 从区间列表中移除重叠的区间
    function FindOverlaps(AItl: TInterval): TList<TInterval>; // 寻找重叠区间
  end;

  TToken = class(TObject)
  private
    FFragment: string; // 对应的片断
  public
    constructor Create(const AFragment: string);
    destructor Destroy; override;

    function IsMatch: Boolean; virtual; abstract;
    function GetEmit: TEmit; virtual; abstract;
    property Fragment: string read FFragment;
  end;

  TMatchToken = class(TToken)
  private
    FEmit: TEmit;
  public
    constructor Create(const AFragment: string; const AEmit: TEmit);
    function IsMatch: Boolean; override;
    function GetEmit: TEmit; override;
  end;

  TFragmentToken = class(TToken)
  public
    function IsMatch: Boolean; override;
    function GetEmit: TEmit; override;
  end;

implementation

uses
  System.SysUtils, System.Generics.Defaults;

var
  U_CompareSize, U_ComparePos: IComparer<TInterval>;

{ TInterval }
constructor TInterval.Create(const AStart, AEnd: Integer);
begin
  FStart := AStart;
  FEnd := AEnd;
end;

function TInterval.Equals(AOther: TObject): Boolean;
begin
  Result := (FStart = TEmit(AOther).GetStart) and (FEnd = TEmit(AOther).GetEnd)
end;

function TInterval.Size: Integer;
begin
  Result := FEnd - FStart + 1;
end;

function TInterval.ToString: string;
begin
  Result := Format('%d : %d', [FStart, FEnd]);
end;

function TInterval.OverlapsWith(const AOther: TInterval): Boolean;
begin
  Result := (FStart <= AOther.GetEnd) and (FEnd >= AOther.GetStart);
end;

function TInterval.OverlapsWith(const APoint: Integer): Boolean;
begin
  Result := (FStart <= APoint) and (FEnd >= APoint);
end;

function IntervalComparerByPos(const ALeft, ARight: TInterval): Integer;
begin
  Result := ALeft.GetStart - ARight.GetStart;
end;

function IntervalComparerBySize(const ALeft, ARight: TInterval): Integer;
begin
  if ALeft.Size < ARight.Size then
    Result := 1
  else if ALeft.Size > ARight.Size then
    Result := -1
  else
    Result := IntervalComparerByPos(ALeft, ARight);
end;

{ TEmit }
constructor TEmit.Create(const AStart, AEnd: Integer; const AKeyword: string);
begin
  inherited Create(AStart, AEnd);
  FKeyword := AKeyword;
end;

function TEmit.ToString: string;
begin
  Result := inherited ToString + ' = ' + FKeyword;
end;

{ TINode }
constructor TIntervalNode.Create(const AItls: TList<TInterval>);
var
  LItl: TInterval;
  LToLeft, LToRight: TList<TInterval>; // 以中点为界靠左/右的区间
begin
  if not FInited then
    Initial;

  FPoint := CalcMedian(AItls);

  LToLeft := TList<TInterval>.Create;
  LToRight := TList<TInterval>.Create;
  try
    for LItl in AItls do
    begin
      if LItl.GetEnd < FPoint then
        LToLeft.Add(LItl)
      else if LItl.GetStart > FPoint then
        LToRight.Add(LItl)
      else
        FIntervals.Add(LItl);
    end;

    if LToLeft.Count > 0 then
      FLeft := TIntervalNode.Create(LToLeft);

    if LToRight.Count > 0 then
      FRight := TIntervalNode.Create(LToRight);
  finally
    FreeAndNil(LToLeft);
    FreeAndNil(LToRight);
  end;
end;

destructor TIntervalNode.Destroy;
var
  LItl: TInterval;
begin
  if Assigned(FLeft) then
    FreeAndNil(FLeft);
  if Assigned(FRight) then
    FreeAndNil(FRight);

  for LItl in FIntervals do
  begin
    LItl.Free;
  end;
  FIntervals.Free;
  inherited;
end;

procedure TIntervalNode.Initial;
begin
  inherited Create();

  FLeft := nil;
  FRight := nil;
  FIntervals := TList<TInterval>.Create;
  FInited := True;
end;

function TIntervalNode.CalcMedian(const AItls: TList<TInterval>): Integer;
var
  LItl: TInterval;
  LStart, LEnd: Integer;
begin
  LStart := -1;
  LEnd := -1;

  for LItl in AItls do
  begin
    if (LItl.GetStart < LStart) or (LStart = -1) then
      LStart := LItl.GetStart;
    if (LItl.GetEnd > LEnd) or (LEnd = -1) then
      LEnd := LItl.GetEnd;
  end;

  Result := (LStart + LEnd) shr 1;
end;

// 添加到重叠区间列表中
// @param AItl 跟此区间重叠
// @param AOverlaps 重叠区间列表
// @param ANewOverlaps 希望将这些区间加入
procedure TIntervalNode.AddToOverlaps(const AItl: TInterval;
  AOverlaps, ANewOverlaps: TList<TInterval>);
var
  LItl: TInterval;
begin
  if not Assigned(ANewOverlaps) then
    Exit;

  try
    for LItl in ANewOverlaps do
    begin
      if not LItl.Equals(AItl) then
        AOverlaps.Add(LItl);
    end;
  finally
    if ANewOverlaps <> FIntervals then
      ANewOverlaps.Free;
  end;
end;

// 寻找重叠
// @param AItl 一个区间，与该区间重叠
// @param direction 方向，表明重叠区间在interval的左边还是右边
function TIntervalNode.CheckForOverlaps(const AItl: TInterval; const ADir: TDirection)
  : TList<TInterval>;
var
  LItl: TInterval;
begin
  Result := TList<TInterval>.Create;
  for LItl in FIntervals do
  begin
    case ADir of
      TDirection.LEFT:
        if LItl.GetStart <= AItl.GetEnd then
          Result.Add(LItl);
      TDirection.RIGHT:
        if LItl.GetEnd >= AItl.GetStart then
          Result.Add(LItl);
    end;
  end;
end;

// 往左边寻找重叠
function TIntervalNode.CheckForOverlapsToTheLeft(const AItl: TInterval): TList<TInterval>;
begin
  Result := CheckForOverlaps(AItl, TDirection.LEFT);
end;

// 往右边寻找重叠
function TIntervalNode.CheckForOverlapsToTheRight(const AItl: TInterval): TList<TInterval>;
begin
  Result := CheckForOverlaps(AItl, TDirection.RIGHT);
end;

// 是对IntervalNode.findOverlaps(TInterval)的一个包装，防止NPE
class function TIntervalNode.FindOverlappingRanges(const aNode: TIntervalNode;
  const AItl: TInterval): TList<TInterval>;
begin
  if Assigned(aNode) then
    Result := aNode.FindOverlaps(AItl)
  else
    Result := nil;
end;

// 寻找与AItl有重叠的区间;返回值由外部释放
function TIntervalNode.FindOverlaps(const AItl: TInterval): TList<TInterval>;
begin
  Result := TList<TInterval>.Create;

  if not Assigned(AItl) then
    Exit;

  if FPoint < AItl.GetStart then
  begin // 右边找找
    AddToOverlaps(AItl, Result, FindOverlappingRanges(FRight, AItl));
    AddToOverlaps(AItl, Result, CheckForOverlapsToTheRight(AItl));
  end
  else if FPoint > AItl.GetEnd then
  begin // 左边找找
    AddToOverlaps(AItl, Result, FindOverlappingRanges(FLeft, AItl));
    AddToOverlaps(AItl, Result, CheckForOverlapsToTheLeft(AItl));
  end
  else
  begin // 否则在当前区间
    AddToOverlaps(AItl, Result, FIntervals);
    AddToOverlaps(AItl, Result, FindOverlappingRanges(FLeft, AItl));
    AddToOverlaps(AItl, Result, FindOverlappingRanges(FRight, AItl));
  end;
end;

{ TIntervalTree }

constructor TIntervalTree.Create(const AItls: TList<TInterval>);
begin
  inherited Create;
  FRootNode := TIntervalNode.Create(AItls);
end;

destructor TIntervalTree.Destroy;
begin
  if Assigned(FRootNode) then
    FreeAndNil(FRootNode);

  if Assigned(FOverlapResult) then
    FreeAndNil(FOverlapResult);

  inherited;
end;

function TIntervalTree.FindOverlaps(AItl: TInterval): TList<TInterval>;
begin
  if Assigned(FOverlapResult) then
    FOverlapResult.Free;
  FOverlapResult := FRootNode.FindOverlaps(AItl);

  Result := FOverlapResult;
end;

procedure TIntervalTree.RemoveOverlaps(var AItls: TList<TInterval>);
var
  LRemoveItls: TList<TInterval>;
  LItl: TInterval;
begin
  // 排序，按照先大小后左端点的顺序
  AItls.Sort(U_CompareSize);

  LRemoveItls := TList<TInterval>.Create;
  try
    for LItl in AItls do
    begin
      // 如果区间已经被移除了，就忽略它
      if LRemoveItls.Contains(LItl) then
        Continue;

      // 否则就移除它
      LRemoveItls.AddRange(FindOverlaps(LItl));
    end;

    // 移除所有的重叠区间
    for LItl in LRemoveItls do
    begin
      AItls.Remove(LItl);
    end;
  finally
    LRemoveItls.Free;
  end;

  // 排序，按照左端顺序
  AItls.Sort(U_ComparePos);
end;

{ TToken }

constructor TToken.Create(const AFragment: string);
begin
  inherited Create;
  FFragment := AFragment;
end;

destructor TToken.Destroy;
begin
  inherited;
end;

{ TMatchToken }
constructor TMatchToken.Create(const AFragment: string; const AEmit: TEmit);
begin
  inherited Create(AFragment);
  FEmit := AEmit;
end;

function TMatchToken.GetEmit: TEmit;
begin
  Result := FEmit;
end;

function TMatchToken.IsMatch: Boolean;
begin
  Result := True;
end;

{ TFragmentToken }
function TFragmentToken.GetEmit: TEmit;
begin
  Result := nil;
end;

function TFragmentToken.IsMatch: Boolean;
begin
  Result := False;
end;

initialization
  U_CompareSize := TComparer<TInterval>.Construct(IntervalComparerBySize);
  U_ComparePos := TComparer<TInterval>.Construct(IntervalComparerByPos);

finalization
  U_CompareSize := nil;
  U_ComparePos := nil;

end.
