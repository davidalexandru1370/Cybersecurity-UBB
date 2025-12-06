package com.example.backend.business.service.interfaces;

import com.example.backend.business.entities.CreateUserDTO;
import com.example.backend.core.domain.User;
import com.example.backend.core.exceptions.ExistingAccountException;

public interface IUserService {
    User createUser(CreateUserDTO createUserDTO) throws ExistingAccountException;

}
