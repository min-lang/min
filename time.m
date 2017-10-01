# calendar, date and time, epoch

lib_time = Dl 'time' : out:Mem? out:Mem

lib_strftime = Dl 'strftime' : out:Mem? size:N? format:S? time:Mem? size:N

lib_gmtime = Dl 'gmtime' : time:Mem? Mem

now _ : Mem =
  out = Mem 8
  Fun.call1 lib_time out
  out

gmtime time:Mem : Mem = Fun.call1 lib_gmtime time

# http://en.wikipedia.org/wiki/ISO_8601
datetime_iso time:Mem : S =
  out = S.new 16
  Fun.call4 lib_strftime out.S.mem 16 '%Y%m%dT%H%M%SZ' time
  out

date_iso time:Mem : S =
  out = S.new 8
  Fun.call4 lib_strftime out.S.mem 8 '%Y%m%d' time
  out

datetime _ : S = 0.now.gmtime.datetime_iso

date _ : S = 0.now.gmtime.date_iso

#
  month = Tag
  	Jan = January
  	Feb = February
  	Mar = March
  	Apr = April
  	May = May
  	Jun = June
  	Jul = July
  	Aug = August
  	Sep = September
  	Oct = October
  	Nov = November
  	Dec = December
    
  day = Tag
  	Mon = Monday
  	Tue = Tuesday
  	Wed = Wednesday
  	Thu = Thursday
  	Fri = Friday
  	Sat = Saturday
    
  month_days = Row 31 28 31 30 31 30 31 31 30 31 30 31
