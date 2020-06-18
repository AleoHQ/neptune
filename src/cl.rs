use std::collections::HashMap;
use std::ptr;
use std::sync::{Arc, Mutex};
use triton::bindings;
use triton::FutharkContext;

const MAX_LEN: usize = 128;

lazy_static! {
    pub static ref FUTHARK_CONTEXT_MAP: Mutex<HashMap<u32, Arc<Mutex<FutharkContext>>>> =
        Mutex::new(HashMap::new());
    pub static ref FUTHARK_CONTEXT_DEFAULT: Arc<Mutex<FutharkContext>> =
        Arc::new(Mutex::new(FutharkContext::new()));
}

#[derive(Debug, Clone, Copy)]
pub enum GPUSelector {
    NvidiaBusId(u32),
}

#[derive(Debug, Clone)]
pub enum ClError {
    DeviceNotFound,
    PlatformNotFound,
    NvidiaBusIdNotAvailable,
    PlatformNameNotAvailable,
    CannotCreateContext,
    CannotCreateQueue,
}
pub type ClResult<T> = std::result::Result<T, ClError>;

fn get_platforms() -> ClResult<Vec<bindings::cl_platform_id>> {
    let mut platforms = [ptr::null_mut(); MAX_LEN];
    let mut num_platforms = 0u32;
    let res = unsafe {
        bindings::clGetPlatformIDs(MAX_LEN as u32, platforms.as_mut_ptr(), &mut num_platforms)
    };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(platforms[..num_platforms as usize].to_vec())
    } else {
        Err(ClError::PlatformNotFound)
    }
}

fn get_platform_name(platform_id: bindings::cl_platform_id) -> ClResult<String> {
    let mut name = [0u8; MAX_LEN];
    let mut len = 0u64;
    let res = unsafe {
        bindings::clGetPlatformInfo(
            platform_id,
            bindings::CL_PLATFORM_NAME as u32,
            MAX_LEN as u64,
            name.as_mut_ptr() as *mut std::ffi::c_void,
            &mut len,
        )
    };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(String::from_utf8(name[..len as usize - 1].to_vec()).unwrap())
    } else {
        Err(ClError::PlatformNameNotAvailable)
    }
}

fn get_platform_by_name(name: &str) -> ClResult<bindings::cl_platform_id> {
    for plat in get_platforms()? {
        if get_platform_name(plat)? == name {
            return Ok(plat);
        }
    }
    Err(ClError::PlatformNotFound)
}

fn get_devices(platform_id: bindings::cl_platform_id) -> ClResult<Vec<bindings::cl_device_id>> {
    let mut devs = [ptr::null_mut(); MAX_LEN];
    let mut num_devs = 0u32;
    let res = unsafe {
        bindings::clGetDeviceIDs(
            platform_id,
            bindings::CL_DEVICE_TYPE_GPU as u64,
            MAX_LEN as u32,
            devs.as_mut_ptr(),
            &mut num_devs,
        )
    };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(devs[..num_devs as usize].to_vec())
    } else {
        Err(ClError::DeviceNotFound)
    }
}

fn get_bus_id(device: bindings::cl_device_id) -> ClResult<u32> {
    let mut ret = [0u8; MAX_LEN];
    let mut len = 0u64;
    let res = unsafe {
        bindings::clGetDeviceInfo(
            device,
            0x4008 as u32,
            MAX_LEN as u64,
            ret.as_mut_ptr() as *mut std::ffi::c_void,
            &mut len,
        )
    };
    if res == bindings::CL_SUCCESS as i32 && len == 4 {
        Ok(to_u32(&ret[..4]))
    } else {
        Err(ClError::NvidiaBusIdNotAvailable)
    }
}

fn get_device_by_nvidia_bus_id(bus_id: u32) -> ClResult<bindings::cl_device_id> {
    for dev in get_all_nvidia_devices()? {
        if get_bus_id(dev)? == bus_id {
            return Ok(dev);
        }
    }

    Err(ClError::DeviceNotFound)
}

fn all_devices() -> ClResult<Vec<bindings::cl_device_id>> {
    let mut devs = Vec::new();
    for platform in get_platforms()? {
        for dev in get_devices(platform)? {
            devs.push(dev);
        }
    }
    Ok(devs)
}

fn get_first_device() -> ClResult<bindings::cl_device_id> {
    let devs = all_devices()?;
    devs.first().map(|d| *d).ok_or(ClError::DeviceNotFound)
}

fn create_context(device: bindings::cl_device_id) -> ClResult<bindings::cl_context> {
    let mut res = 0i32;
    let context = unsafe {
        bindings::clCreateContext(
            ptr::null(),
            1,
            [device].as_mut_ptr(),
            None,
            ptr::null_mut(),
            &mut res,
        )
    };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(context)
    } else {
        Err(ClError::CannotCreateContext)
    }
}

fn create_queue(
    context: bindings::cl_context,
    device: bindings::cl_device_id,
) -> ClResult<bindings::cl_command_queue> {
    let mut res = 0i32;
    let context = unsafe { bindings::clCreateCommandQueue(context, device, 0, &mut res) };
    if res == bindings::CL_SUCCESS as i32 {
        Ok(context)
    } else {
        Err(ClError::CannotCreateQueue)
    }
}

impl GPUSelector {
    pub fn get_bus_id(&self) -> ClResult<u32> {
        match self {
            GPUSelector::NvidiaBusId(bus_id) => Ok(*bus_id),
        }
    }
}

fn create_futhark_context(device: bindings::cl_device_id) -> ClResult<FutharkContext> {
    unsafe {
        let context = create_context(device)?;
        let queue = create_queue(context, device)?;

        let ctx_config = bindings::futhark_context_config_new();
        let ctx = bindings::futhark_context_new_with_command_queue(ctx_config, queue);
        Ok(FutharkContext {
            context: ctx,
            config: ctx_config,
        })
    }
}

pub fn get_all_nvidia_devices() -> ClResult<Vec<bindings::cl_device_id>> {
    Ok(get_devices(get_platform_by_name("NVIDIA CUDA")?)?)
}

pub fn get_all_nvidia_bus_ids() -> ClResult<Vec<u32>> {
    let mut bus_ids = Vec::new();
    for dev in get_all_nvidia_devices()? {
        bus_ids.push(get_bus_id(dev)?);
    }
    bus_ids.sort_unstable();
    bus_ids.dedup();
    Ok(bus_ids)
}

pub fn futhark_context(selector: GPUSelector) -> ClResult<Arc<Mutex<FutharkContext>>> {
    let mut map = FUTHARK_CONTEXT_MAP.lock().unwrap();
    let bus_id = selector.get_bus_id()?;
    if !map.contains_key(&bus_id) {
        let device = get_device_by_nvidia_bus_id(bus_id)?;
        let context = create_futhark_context(device)?;
        map.insert(bus_id, Arc::new(Mutex::new(context)));
    }
    Ok(Arc::clone(&map[&bus_id]))
}

pub fn default_futhark_context() -> ClResult<Arc<Mutex<FutharkContext>>> {
    Ok(Arc::clone(&FUTHARK_CONTEXT_DEFAULT))
}

fn to_u32(inp: &[u8]) -> u32 {
    (inp[0] as u32) + ((inp[1] as u32) << 8) + ((inp[2] as u32) << 16) + ((inp[3] as u32) << 24)
}

#[cfg(test)]
#[cfg(all(feature = "gpu", not(target_os = "macos")))]
mod tests {
    use super::*;

    #[test]
    fn test_bus_id_uniqueness() {
        let devices = get_all_nvidia_devices().unwrap();
        let bus_ids = get_all_nvidia_bus_ids().unwrap();
        assert_eq!(devices.len(), bus_ids.len());
    }
}
